#!/usr/bin/env python3
"""Count this session's token use EXACTLY, from the usage records in the transcripts.

Every assistant record in a Claude Code transcript carries a `usage` object with
input_tokens, output_tokens, cache_creation_input_tokens and
cache_read_input_tokens for that one request. Summing them is a measurement, not
an estimate - which matters, because the obvious proxy is badly wrong in both
directions:

  * transcript BYTES are linear in the conversation, while billed input is
    roughly quadratic in turns: every turn re-reads the whole prefix. A
    byte-based estimate therefore undercounts a long main thread heavily.
  * most of that re-read is CACHE READ, which is billed at a fraction of fresh
    input, so counting it at face value overcounts cost.

So this reports the four categories separately and never collapses them into one
"cost" number, because only the account knows the rates.
"""

from __future__ import annotations

import json
import pathlib
import re
import sys
from typing import Final

SESSION: Final = "731ccd8c-0494-56c8-b77c-6e2443ae238b"
MAIN: Final = pathlib.Path(f"/root/.claude/projects/-home-user-pequalnp-proofs/{SESSION}.jsonl")
TASKS: Final = pathlib.Path(f"/tmp/claude-0/-home-user-pequalnp-proofs/{SESSION}/tasks")

FIELDS: Final = (
    "input_tokens",
    "output_tokens",
    "cache_creation_input_tokens",
    "cache_read_input_tokens",
)


def tally(path: pathlib.Path) -> tuple[dict[str, int], int]:
    """(summed usage, number of requests) for one transcript."""
    acc = dict.fromkeys(FIELDS, 0)
    n = 0
    try:
        with open(path, errors="replace") as fh:
            for line in fh:
                if '"usage"' not in line:
                    continue
                try:
                    rec = json.loads(line)
                except json.JSONDecodeError:
                    continue
                msg = rec.get("message")
                u = msg.get("usage") if isinstance(msg, dict) else None
                if not isinstance(u, dict):
                    continue
                n += 1
                for f in FIELDS:
                    v = u.get(f)
                    if isinstance(v, int):
                        acc[f] += v
    except OSError:
        pass
    return acc, n


def show(label: str, acc: dict[str, int], n: int) -> None:
    fresh = acc["input_tokens"] + acc["cache_creation_input_tokens"]
    sys.stdout.write(
        f"{label}\n"
        f"    requests              {n:>12,}\n"
        f"    fresh input           {acc['input_tokens']:>12,}\n"
        f"    cache WRITE           {acc['cache_creation_input_tokens']:>12,}\n"
        f"    cache READ            {acc['cache_read_input_tokens']:>12,}\n"
        f"    output                {acc['output_tokens']:>12,}\n"
        f"    -- uncached input     {fresh:>12,}\n"
        f"    -- all input          {fresh + acc['cache_read_input_tokens']:>12,}\n"
    )


def main() -> int:
    main_acc, main_n = tally(MAIN)
    show("MAIN THREAD", main_acc, main_n)

    agents = sorted(
        (p for p in TASKS.glob("*.output") if re.fullmatch(r"a[0-9a-f]{16}", p.stem)),
        key=lambda q: -q.stat().st_size,
    )
    tot = dict.fromkeys(FIELDS, 0)
    tot_n = 0
    per: list[tuple[str, int]] = []
    for p in agents:
        a, n = tally(p)
        tot_n += n
        for f in FIELDS:
            tot[f] += a[f]
        per.append((p.stem, a["output_tokens"] + a["input_tokens"] + a["cache_creation_input_tokens"]))
    sys.stdout.write(f"\nAGENTS: {len(agents)} transcripts\n")
    show("  (summed)", tot, tot_n)

    gt = {f: main_acc[f] + tot[f] for f in FIELDS}
    fresh = gt["input_tokens"] + gt["cache_creation_input_tokens"]
    sys.stdout.write(
        "\nSESSION TOTAL\n"
        f"    uncached input (billed at full rate)  {fresh:>12,}\n"
        f"    cache read (billed at a fraction)     {gt['cache_read_input_tokens']:>12,}\n"
        f"    output                                {gt['output_tokens']:>12,}\n"
        f"    agents' share of uncached input       "
        f"{100 * (tot['input_tokens'] + tot['cache_creation_input_tokens']) / max(fresh, 1):>11.0f}%\n"
    )
    if per:
        per.sort(key=lambda kv: -kv[1])
        sys.stdout.write("\nmost expensive agents, by uncached input + output:\n")
        for aid, c in per[:8]:
            sys.stdout.write(f"    {c:>10,}  {aid}\n")
        costs = [c for _, c in per]
        sys.stdout.write(
            f"\n    mean per agent {sum(costs) // len(costs):,}"
            f"   median {sorted(costs)[len(costs) // 2]:,}\n"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
