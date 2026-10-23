import json

HEX = "ab" * 8


def entry(n: int, stars: int | None = 4, **over) -> dict:
    eid = f"{n:012x}{HEX}"
    e = {
        "id": eid, "name": f"lemma_{n}", "kind": "theorem",
        "statement": f"theorem lemma_{n} (a : Nat) : a + {n} = {n} + a",
        "closure": f"theorem lemma_{n} (a : Nat) : a + {n} = {n} + a := by\n  omega",
        "origin": "verified", "savedAt": "2026-10-22T00:00:00Z", "attempt": 1, "isTarget": False, "quality": None if stars is None else {"s": stars, "u": 0},
        "harness": {"keptAt": "2026-10-22T01:00:00Z", "ticketAgeMs": 3_600_000, "buildId": "c" * 64,
                    "receipt": {"ok": True, "seconds": 3590, "verifyOk": 60, "verifyFail": 40, "searches": 3, "attempts": 4, "model": "claude-sonnet-5-5", "strategy": "control-lucid-iv"}},
    }
    e.update(over)
    return e


def candidate(ns: list[int] | None = None, **over) -> dict:
    return {"author": "ada", "target": "erdos-396", "entries": [entry(n) for n in (ns or [1, 2, 3])], **over}


def fake_review(verdicts: dict | None = None, ran=("style", "naming", "docs", "api", "dedupe", "reuse", "hoist")):
    """review_fn double: accept everything unless `verdicts` (entry id -> dict) says otherwise"""
    def review(modules, facts):
        out = {}
        for eid in facts:
            out[eid] = (verdicts or {}).get(eid) or {"verdict": "accept", "codes": [], "merit": ["five_stars"]}
        return out, set(ran)

    return review


def j(x) -> str:
    return json.dumps(x, sort_keys=True)
