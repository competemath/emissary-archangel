#!/usr/bin/env python3
"""round-summary.py <metrics.tsv> [title] [seconds between samples] — reads what runner-watch.sh wrote and prints a markdown summary (for $GITHUB_STEP_SUMMARY):
modules built at the start and end of the round, the lowest free memory, the biggest process and when, and the pace per hour."""
import csv, sys

def main(path, title="Build round", every=60):
    rows = list(csv.DictReader(open(path), delimiter="\t"))
    if not rows:
        print(f"### {title}\n\nNo samples were written.")
        return
    num = lambda r, k: int(r[k]) if r[k].lstrip("-").isdigit() else None
    built = [b for b in (num(r, "built") for r in rows) if b is not None]
    free = [(f, r["time"]) for r in rows if (f := num(r, "free_mb")) is not None]
    top = [(t, r["time"], r["top_name"]) for r in rows if (t := num(r, "top_mb")) is not None]
    out = [f"### {title}", "", f"- samples: {len(rows)} (from {rows[0]['time']} to {rows[-1]['time']} UTC)"]
    if built:
        out.append(f"- modules built (.olean files): {built[0]} at the start, {built[-1]} at the end, +{built[-1] - built[0]}")
        hours = max(len(rows) - 1, 1) * int(every) / 3600
        out.append(f"- pace: about {round((built[-1] - built[0]) / hours)} modules an hour")
    if free:
        f, t = min(free)
        out.append(f"- lowest free memory: {f} MB at {t} UTC")
    if top:
        m, t, name = max(top)
        out.append(f"- biggest process: {m} MB ({name}) at {t} UTC")
    print("\n".join(out))

if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("usage: round-summary.py <metrics.tsv> [title] [seconds]")
    main(*sys.argv[1:4])
