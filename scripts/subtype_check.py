import sys
import argparse
import os
import subprocess
import shutil
import locale
import re
from pathlib import Path
from runner import invoc_cmd, run_for_dir_from_cli

cmd_prefix = "opam exec -- dune exec --no-buffer -- bin/main.exe subtype-check".split(
    " "
)
config_file_name = "meta-config.json"
workdir = "underapproximation_type"
verbose = True


def check_res_for_true_result(res: subprocess.CompletedProcess[bytes]):
    # A run may print several verdicts; any false, or a crash after a true, fails it.
    stdout = str(res.stdout)
    if res.returncode != 0 or "Result: false" in stdout or "Result: true" not in stdout:
        print("Error: subtype-check failed")
        print(res.args)
        return True
    return False


def navigate_dir_and_run(dir_str, config_file_name):
    meta_config_file = "{}/{}".format(dir_str, config_file_name)
    if not (os.path.exists(meta_config_file)):
        for f in os.listdir(dir_str):
            pp = "{}/{}".format(dir_str, f)
            if os.path.isdir(pp):
                navigate_dir_and_run(pp, config_file_name)
    else:
        tests_dir = "{}/subtyping_tests".format(dir_str)
        if not os.path.isdir(tests_dir):
            return
        for filename in sorted(os.listdir(tests_dir)):
            matches = re.search(r".*\.ml$", filename, re.MULTILINE)
            filename = "{}/{}".format(tests_dir, filename)
            if matches:
                cmd = cmd_prefix + ["-config", meta_config_file, filename]

                invoc_cmd(verbose, cmd, check_res_for_true_result, None, cwd=None)


def synth_func(dir_str):
    navigate_dir_and_run(dir_str, config_file_name)


if __name__ == "__main__":
    run_for_dir_from_cli(workdir, synth_func)
