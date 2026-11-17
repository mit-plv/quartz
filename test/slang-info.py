#!/usr/bin/env python3
import json
import subprocess
import sys

proc = subprocess.run(
    [sys.argv[1], "-q", "--diag-json", "/dev/stdout", *sys.argv[2:]],
    capture_output=True, text=True)
if proc.returncode != 0:
    sys.stderr.write(proc.stderr or f"slang exited with {proc.returncode}\n")
    sys.exit(proc.returncode)
prefix = "$info encountered: "
infos = [d["message"].removeprefix(prefix)
         for d in json.loads(proc.stdout) if d["message"].startswith(prefix)]
if len(infos) != 1:
    sys.exit(f"{proc.stderr}expected exactly one $info, got {len(infos)}")
print(infos[0])
