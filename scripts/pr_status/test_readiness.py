"""Contract tests using the actual pinned Auto-merge engine, without network calls."""

import copy
import json
import subprocess
import unittest
from unittest.mock import patch

import readiness


HEAD = "current"
NOW = 1700000000
PR = {"number": 1, "state": "open", "head": {"sha": HEAD}, "base": {"ref": "main"},
      "draft": False, "labels": []}
STATUSES = {"build": "success", "scope": "success", "bump-guard": "success"}
DIFF = "diff --git a/TauCeti/X.lean b/TauCeti/X.lean\n"


def board(states=None, head=HEAD, mode="commit", updated="2026-09-16T01:00:00Z", extra=None):
    if states is None:
        states = {r: "green" for r in readiness.engine().DEFAULT_RUBRICS}
    meta = {"head_sha": head, "mode": mode, "states": states}
    meta.update(extra or {})
    return {"body": "<!--tauceti-scoreboard--><!--tauceti-meta:v1 " + json.dumps(meta) + "-->",
            "updated_at": updated}


def marker(head=HEAD, expires=NOW + 60):
    return {"body": "<!--tauceti-review-in-progress " +
            json.dumps({"head": head, "expires_at": expires}) + "-->"}


class GateContract(unittest.TestCase):
    def check(self, expected, comments=None, statuses=None, diff=DIFF, pr=None):
        result = readiness.classify(pr or PR, [board()] if comments is None else comments,
                                    STATUSES if statuses is None else statuses, diff, NOW)
        self.assertEqual(result["category"], expected, result)
        self.assertEqual(result["eligible"], expected == "ready-to-merge")
        if result["eligible"]:
            self.assertTrue(result["gate"]["merge"])
        return result

    def test_complete_current_review_and_all_guards_are_ready(self):
        self.check("ready-to-merge")

    def test_scope_failure_for_human_files_is_not_ready(self):
        self.check("needs-human-review", statuses=dict(STATUSES, scope="failure"),
                   diff="diff --git a/web/examples/Examples.lean b/web/examples/Examples.lean\n")

    def test_green_scope_does_not_override_forbidden_path(self):
        self.check("needs-human-review", diff="diff --git a/scripts/x.py b/scripts/x.py\n")

    def test_missing_scope_is_pending_and_failed_scope_is_ci_failure(self):
        self.check("awaiting-CI", statuses={"build": "success"})
        self.check("ci-failed", statuses=dict(STATUSES, scope="failure"))

    def test_pin_requires_bump_guard(self):
        diff = "diff --git a/lake-manifest.json b/lake-manifest.json\n"
        self.check("awaiting-CI", statuses=dict(STATUSES, **{"bump-guard": ""}), diff=diff)
        self.check("ci-failed", statuses=dict(STATUSES, **{"bump-guard": "failure"}), diff=diff)
        self.check("ready-to-merge", diff=diff)

    def test_stale_and_incomplete_scoreboards_cannot_be_ready(self):
        self.check("awaiting-review", comments=[board(head="old")])
        self.check("awaiting-review", comments=[board(states={"correctness": "green"})])
        self.check("awaiting-review", comments=[board(mode="init")])
        self.check("awaiting-review", comments=[])

    def test_live_review_delays_enqueue_even_after_green_review(self):
        self.check("review-in-progress", comments=[board(), marker()])
        self.check("ready-to-merge", comments=[board(), marker(expires=NOW)])
        self.check("ready-to-merge", comments=[board(), marker(head="old")])

    def test_selects_completed_current_head_not_newer_old_head_or_init(self):
        self.check("ready-to-merge", comments=[board(), board(head="old", states={}, updated="z")])
        self.check("ready-to-merge", comments=[board(), board(mode="init", states={}, updated="z")])

    def test_newer_completed_blocking_review_supersedes_approval(self):
        states = {r: "green" for r in readiness.engine().DEFAULT_RUBRICS}
        states["proof-quality"] = "blocking_request"
        self.check("awaiting-author", comments=[board(), board(states=states, updated="z")])

    def test_legacy_runs_cannot_substitute_for_complete_table(self):
        old = board(states={}, extra={"runs": [{"verdict": "approve"}]})
        self.check("awaiting-review", comments=[old])
        old["body"] += "\n" + "\n".join(
            f"| ✅ | [{r}](url) | approved | judge | summary |"
            for r in readiness.engine().DEFAULT_RUBRICS)
        self.check("ready-to-merge", comments=[old])

    def test_ci_failure_and_missing_build_are_never_ready(self):
        self.check("ci-failed", statuses=dict(STATUSES, build="failure"))
        self.check("awaiting-CI", statuses=dict(STATUSES, build="pending"))
        self.check("awaiting-CI", statuses=dict(STATUSES, build=""))

    def test_queue_independent_routing(self):
        self.check("awaiting-dependency", pr=dict(PR, base={"ref": "parent"}))
        self.check("on-hold", pr=dict(PR, draft=True))
        for label in readiness.sweep_engine().KEEP_LABELS:
            self.check("on-hold", pr=dict(PR, labels=[{"name": label.upper()}]))
        self.check(None, pr=dict(PR, state="closed"))

    def test_explicit_merge_conflict_is_not_ready(self):
        self.check("awaiting-author", pr=dict(PR, mergeable=False))


class ReadEvidence(unittest.TestCase):
    @patch.object(readiness.subprocess, "check_output", return_value=DIFF)
    @patch.object(readiness.core, "gh_api")
    def test_paginated_statuses_choose_newest_and_head_change_invalidates_result(self, api, diff):
        moved = copy.deepcopy(PR)
        moved["head"]["sha"] = "moved"
        rows = [dict(id=2, context="build", state="success"),
                dict(id=1, context="build", state="failure"),
                dict(id=3, context="scope", state="success")]
        api.side_effect = [json.dumps(PR), json.dumps(board()),
                           "\n".join(map(json.dumps, rows)), json.dumps(moved)]
        result = readiness.assess(1, repo="owner/repo", now=NOW)
        self.assertTrue(result["gate"]["merge"])
        self.assertFalse(result["eligible"])
        self.assertEqual(result["head"], "moved")
        self.assertTrue(api.call_args_list[1].kwargs["paginate"])
        self.assertTrue(api.call_args_list[2].kwargs["paginate"])

    @patch.object(readiness.subprocess, "check_output")
    @patch.object(readiness.core, "gh_api", side_effect=RuntimeError("rate limited"))
    def test_failed_read_is_not_a_merge_verdict(self, api, diff):
        with self.assertRaisesRegex(RuntimeError, "rate limited"):
            readiness.assess(1)
        diff.assert_not_called()


if __name__ == "__main__":
    unittest.main()
