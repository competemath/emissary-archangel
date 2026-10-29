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
        # the previous round's build is unpacked after the first samples, so the count jumps from 0 to tens of thousands within a few minutes
        # (compiling adds a few modules a minute): when there is such a jump (500 or more between two samples) the round's own work starts
        # after the last one; with no jump it starts at the first sample
        jumps = [k + 1 for k in range(len(built) - 1) if built[k + 1] - built[k] >= 500]
        i = jumps[-1] if jumps else 0
        where = "once the earlier build was unpacked" if jumps else "at the start"
        out.append(f"- modules built (.olean files): {built[i]} {where}, {built[-1]} at the end, +{built[-1] - built[i]}")
        hours = max(len(built) - 1 - i, 1) * int(every) / 3600
        out.append(f"- pace: about {round((built[-1] - built[i]) / hours)} modules an hour")
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
