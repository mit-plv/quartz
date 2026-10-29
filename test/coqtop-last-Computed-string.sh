#!/usr/bin/env python3
import re
import resource
import subprocess
import sys

_, hard = resource.getrlimit(resource.RLIMIT_STACK)
resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))


def main():
    proc = subprocess.run(
        ["coqtop", *sys.argv[1:]],
        input=sys.stdin.read(),
        text=True,
        capture_output=True,
    )
    matches = re.findall(
        r'^\s*=\s*"((?:[^"]|"")*)"(?:\s*:\s*string)?',
        proc.stdout,
        re.MULTILINE,
    )
    if proc.returncode != 0 or not matches:
        if proc.stderr:
            sys.stderr.write(proc.stderr.replace("Rocq < ", ""))
        if not matches:
            sys.stderr.write(
                "coqtop produced no result string; first bytes: "
                + proc.stdout[:2000]
                + "\n"
            )
        return proc.returncode if proc.returncode != 0 else 1
    print(matches[-1].replace('""', '"'))
    return 0


if __name__ == "__main__":
    sys.exit(main())
