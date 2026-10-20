import os
import re
import subprocess
import sys
import time

from runner import run_for_dir_from_cli

# The prebuilt synthesizer, relative to the `underapproximation_type` CWD that
# `run_for_dir_from_cli` establishes; `dune build` from Cobb/ refreshes it.
main_exe = "../_build/default/bin/main.exe"
variant_re = re.compile(r"_gen_synth_prog[0-9]+\.ml$")


def variants(dir_str):
    for root, _, files in sorted(os.walk(dir_str)):
        for f in sorted(files):
            if variant_re.search(f):
                yield os.path.join(root, f)


# Serial on purpose: a second Z3-heavy abduction alongside can time out an early
# verifier query and over-include the coverage, which the committed `.abd` then
# rejects as a spurious mismatch.
def run_abduction(dir_str):
    if not os.path.exists(main_exe):
        sys.exit(f"{main_exe} not built; run `dune build` from Cobb/")
    failed = []
    start = time.monotonic()
    for f in variants(dir_str):
        t0 = time.monotonic()
        res = subprocess.run([main_exe, "abduction", f], capture_output=True, text=True)
        status = "ok  " if res.returncode == 0 else "FAIL"
        print(f"{status} {time.monotonic() - t0:5.1f}s {os.path.relpath(f, dir_str)}")
        if res.returncode != 0:
            failed.append(f)
            print("\n".join(res.stderr.splitlines()[-5:]), file=sys.stderr)
    print(f"{len(failed)} failed, {time.monotonic() - start:.0f}s")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    run_for_dir_from_cli("underapproximation_type", run_abduction)
