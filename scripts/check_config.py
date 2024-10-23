import sys
import os
import subprocess
import re

from runner import invoc_cmd, run_for_dir_from_cli, rescode_non_zero

cmd_prefix = "opam exec -- dune exec Cobb --no-buffer -- config".split(" ")
config_file = "meta-config.json"
workdir = "underapproximation_type"
verbose = True


def run_config_check(dir_str):
    meta_config_file = "{}/{}".format(dir_str, config_file)
    if not (os.path.exists(meta_config_file)):
        for f in os.listdir(dir_str):
            pp = "{}/{}".format(dir_str, f)
            if os.path.isdir(pp):
                run_config_check(pp)
    else:
        for filename in os.listdir(dir_str):
            matches = re.search(r"prog\.ml", filename, re.MULTILINE)
            filename = "{}/{}".format(dir_str, filename)
            if matches:
                cmd = cmd_prefix + [filename]
                invoc_cmd(verbose, cmd, rescode_non_zero, None, cwd=None)


if __name__ == "__main__":
    run_for_dir_from_cli(workdir, run_config_check)
