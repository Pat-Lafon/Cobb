import sys
import os
import subprocess
import re
from pathlib import Path

cmd_prefix = "dune exec Cobb --no-buffer --".split(" ")
config_file = "meta-config.json"
workdir = "underapproximation_type"
verbose = True


from runner import invoc_cmd


def run_check_config_aux(file_name):
    cmd = cmd_prefix + ["config", file_name]
    invoc_cmd(verbose, cmd, None, cwd=None)


def run_config_check(dir_str):
    meta_config_file = "{}/{}".format(dir_str, config_file)
    if not (os.path.exists(meta_config_file)):
        for f in os.listdir(dir_str):
            pp = "{}/{}".format(dir_str, f)
            if os.path.isdir(pp):
                run_config_check(pp)
    else:
        for filename in os.listdir(dir_str):
            matches = re.search(r"prog.ml", filename, re.MULTILINE)
            if matches:
                run_check_config_aux("{}/{}".format(dir_str, filename))


if __name__ == "__main__":
    dir_str = sys.argv[1]

    directory = Path(dir_str)
    assert directory.is_dir()

    working_dir = Path(workdir)
    assert working_dir.is_dir()

    assert directory.is_relative_to(working_dir)
    os.chdir(working_dir)
    directory = os.path.relpath(directory, working_dir)

    run_config_check(directory)
