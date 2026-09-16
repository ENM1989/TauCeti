"""Read-only adapter to the exact TauCetiReview gate used by Auto-merge.

Labels and pipeline health call the deployed gate, rather than implementing a
second interpretation of scoreboards. Set TAUCETI_REVIEW_RUNNER to its pinned
checkout's runner directory (the workflows provision it without credentials).
"""

import functools
from datetime import datetime, timezone
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

import core

@functools.lru_cache(maxsize=1)
def engine():
    runner = Path(os.environ.get("TAUCETI_REVIEW_RUNNER", ".tauceti-review/runner")).resolve()
    if not (runner / "merge_from_scoreboard.py").is_file():
        raise RuntimeError("Pinned review engine missing; set TAUCETI_REVIEW_RUNNER")
    sys.path.insert(0, str(runner))
    return importlib.import_module("merge_from_scoreboard")


def sweep_engine():
    engine()
    return importlib.import_module("sweep")


def routing_state(pr):
    labels = {label["name"].lower() for label in pr.get("labels", [])}
    return (pr["head"]["sha"], pr["base"]["ref"], pr["state"], pr.get("draft"),
            labels & sweep_engine().KEEP_LABELS)


def classify(pr, comments, statuses, diff, now=None):
    """Pure evaluation of a fetched PR. Reservations and queue capacity are separate."""
    gate = engine()
    head = pr["head"]["sha"]
    result = {"head": head, "number": pr["number"], "eligible": False,
              "category": None, "reason": "PR is closed", "gate": None}
    if pr["state"] != "open":
        return result
    verdict = gate.decide_from_comments(
        comments, head, set(gate.DEFAULT_RUBRICS), diff,
        statuses.get("build", ""), statuses.get("bump-guard", ""),
        scope=statuses.get("scope", ""), now=now)
    result["gate"] = verdict
    result["reason"] = verdict["reason"]
    labels = {label["name"].lower() for label in pr.get("labels", [])}
    if pr.get("draft") or labels & sweep_engine().KEEP_LABELS:
        result.update(category="on-hold", reason="PR is a draft or intentionally held")
    elif pr["base"]["ref"] != "main":
        result.update(category="awaiting-dependency", reason="PR targets another branch, not main")
    elif pr.get("mergeable") is False:
        result.update(category="awaiting-author", reason="GitHub reports a merge conflict with the base")
    elif verdict["merge"]:
        result.update(category="ready-to-merge", eligible=True)
    elif statuses.get("build", "").lower() != "success":
        result["category"] = ("ci-failed" if statuses.get("build", "").lower()
                              in {"failure", "error"} else "awaiting-CI")
    else:
        latest = gate.latest_current_scoreboard(comments, head)
        if latest is None or latest[1].get("mode") == "init":
            result["category"] = ("review-in-progress" if gate.has_live_review(comments, head, now)
                                  else "awaiting-review")
        elif not verdict["review_safe"]:
            board, meta = latest
            states = meta.get("states")
            if not isinstance(states, dict) or not states:
                states = gate.states_from_table(board.get("body"))
            blocking = any(states.get(r) in {"blocking_request", "blocking_block"}
                           for r in gate.DEFAULT_RUBRICS)
            result["category"] = ("awaiting-author" if blocking else
                                  "review-in-progress" if gate.has_live_review(comments, head, now)
                                  else "awaiting-review")
        elif gate.has_live_review(comments, head, now):
            result["category"] = "review-in-progress"
        else:
            paths = gate.changed_paths(diff)
            human = not paths or any(not (p.startswith("TauCeti/") or p in gate.DEFAULT_ALLOW)
                                     for p in paths)
            if human:
                result["category"] = "needs-human-review"
            else:
                guards = [statuses.get("scope", "")]
                if paths & {"lake-manifest.json", "lean-toolchain"}:
                    guards.append(statuses.get("bump-guard", ""))
                result["category"] = ("ci-failed" if any(g.lower() in {"failure", "error"}
                                                        for g in guards) else "awaiting-CI")
    return result


def json_rows(path, fields):
    return [json.loads(line) for line in core.gh_api(path, jq=fields, paginate=True).splitlines()
            if line.strip()]


def assess(pr, repo=None, now=None):
    """Fetch fresh evidence and bind the reported decision to the current head."""
    repo = repo or core.REPO
    number = int(pr)
    path = f"/repos/{repo}/pulls/{number}"
    current = json.loads(core.gh_api(path))
    if current["state"] != "open":
        return {"number": number, "head": current["head"]["sha"], "eligible": False,
                "category": None, "reason": "PR is closed", "gate": None}
    head = current["head"]["sha"]
    comments = json_rows(f"/repos/{repo}/issues/{number}/comments?per_page=100",
                         ".[] | {body, updated_at, created_at}")
    rows = json_rows(f"/repos/{repo}/commits/{head}/statuses?per_page=100",
                     ".[] | {id, context, state}")
    statuses = {}
    for row in sorted(rows, key=lambda r: r["id"]):
        statuses[row["context"]] = row["state"]
    diff = subprocess.check_output(["gh", "pr", "diff", str(number), "--repo", repo], text=True)
    result = classify(current, comments, statuses, diff, now=now)
    after = json.loads(core.gh_api(path))
    # A read spans several API calls. Never write ready for a head/base/state that moved.
    if routing_state(after) != routing_state(current):
        result.update(eligible=False, category="awaiting-CI" if after["state"] == "open" else None,
                      reason="PR changed while collecting merge evidence; awaiting reconciliation",
                      head=after["head"]["sha"])
    elif after.get("mergeable") is False and result["eligible"]:
        result.update(eligible=False, category="awaiting-author",
                      reason="GitHub reports a merge conflict with the base")
    result["checked_at"] = int(time.time()) if now is None else now
    return result


def queue_snapshot(repo):
    """Read the queue once per report, using Auto-merge's reservation policy."""
    sweep = sweep_engine()
    sweep.REPO = repo
    entries = sweep.queue_entries()
    return {"known": True, "numbers": [e["number"] for e in entries],
            "reservation_holder": sweep.reservation_holder(entries, datetime.now(timezone.utc))}


def audit(snapshot):
    """Validate current stages without trusting labels; retain failures as unknown."""
    repo = snapshot["repo"]
    results = {}
    for pr in snapshot["prs"]:
        if pr["state"] != "OPEN" or pr["is_draft"]:
            continue
        number = pr["number"]
        try:
            results[str(number)] = assess(number, repo=repo)
        except (RuntimeError, subprocess.CalledProcessError, KeyError, ValueError) as exc:
            results[str(number)] = {"number": number, "eligible": None,
                                    "category": None, "reason": str(exc)}
    try:
        queue = queue_snapshot(repo)
    except (RuntimeError, subprocess.CalledProcessError, KeyError, ValueError) as exc:
        queue = {"known": False, "reason": str(exc)}
    return {"checked_at": int(time.time()), "prs": results, "queue": queue}
