"""Bounded, dependency-ordered Lake build for memory-constrained P079 replay.

Run from the candidate project root. This only builds local Lean modules; it
does not publish, submit, update dependencies, or replace Comparator.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path


IMPORT = re.compile(
    r"^(?:(?:public|meta)\s+)*import(?:\s+all)?\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$",
    re.MULTILINE,
)
active_process: subprocess.Popen[str] | None = None


def stop_active(signum: int, _frame: object) -> None:
    if active_process is not None and active_process.poll() is None:
        os.killpg(active_process.pid, signal.SIGTERM)
    raise SystemExit(128 + signum)


def main() -> int:
    global active_process
    signal.signal(signal.SIGINT, stop_active)
    signal.signal(signal.SIGTERM, stop_active)
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", default="Registry.P079.Solution")
    parser.add_argument("--start-at", type=int, default=1)
    parser.add_argument("--limit", type=int)
    parser.add_argument("--timeout-per-module", type=int, default=900)
    args = parser.parse_args()
    root = Path.cwd()
    sources = {
        ".".join(path.relative_to(root).with_suffix("").parts): path
        for path in root.rglob("*.lean")
        if ".lake" not in path.parts and path.name != "lakefile.lean"
    }
    if args.target not in sources:
        raise SystemExit(f"target not in candidate: {args.target}")
    ordered: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(name: str) -> None:
        if name in visited:
            return
        if name in visiting:
            raise RuntimeError(f"local import cycle at {name}")
        visiting.add(name)
        for imported in IMPORT.findall(sources[name].read_text(encoding="utf-8-sig")):
            if imported in sources:
                visit(imported)
        visiting.remove(name)
        visited.add(name)
        ordered.append(name)

    visit(args.target)
    if not 1 <= args.start_at <= len(ordered):
        raise SystemExit(f"--start-at must be between 1 and {len(ordered)}")
    selected = ordered[args.start_at - 1 :]
    if args.limit is not None:
        selected = selected[: args.limit]
    log = root / ".local/P079-serial-build.jsonl"
    log.parent.mkdir(parents=True, exist_ok=True)
    print(f"local closure: {len(ordered)} modules; this pass: {len(selected)}", flush=True)
    with log.open("a", encoding="utf-8") as stream:
        for index, name in enumerate(selected, args.start_at):
            for attempt in (1, 2):
                start = time.monotonic()
                process = subprocess.Popen(
                    ["lake", "--wfail", "--fail-fast", "build", name],
                    cwd=root,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                    start_new_session=True,
                )
                active_process = process
                try:
                    output, _ = process.communicate(timeout=args.timeout_per_module)
                    code = process.returncode
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    output, _ = process.communicate()
                    code = 124
                active_process = None
                elapsed = round(time.monotonic() - start, 2)
                row = {"module": name, "index": index, "total": len(ordered),
                       "attempt": attempt, "seconds": elapsed, "exit_code": code}
                stream.write(json.dumps(row) + "\n")
                stream.flush()
                print(f"{index}/{len(ordered)} {name} attempt {attempt}: "
                      f"exit {code} in {elapsed}s", flush=True)
                if not code:
                    break
                failure_log = root / f".local/P079-serial-failure-{index}-{attempt}.log"
                failure_log.write_text(output, encoding="utf-8")
                truncated_trace = (
                    "offset 0: unexpected end of input" in output
                    and ".trace:" in output
                    and "error: build failed" in output
                    and not re.search(r"(?m)^error: (?!build failed$)", output)
                    and code != 124
                )
                if attempt == 1 and truncated_trace:
                    print(f"retrying exact truncated-trace failure; log: {failure_log}",
                          file=sys.stderr, flush=True)
                    continue
                print(f"failure log: {failure_log}", file=sys.stderr, flush=True)
                print(output[-8000:], file=sys.stderr, flush=True)
                return code
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
