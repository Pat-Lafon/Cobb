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
    if "Result: true" not in str(res.stdout):
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
        from multiprocessing import Pool

        pool = Pool()

        multiple_res = []
        for filename in os.listdir(dir_str):
            matches = re.search(r".*\.ml", filename, re.MULTILINE)
            filename = "{}/{}".format(dir_str, filename)
            if matches:
                cmd = cmd_prefix + [meta_config_file, filename]

                res = pool.apply_async(
                    invoc_cmd,
                    args=[verbose, cmd, check_res_for_true_result, None],
                    kwds={"cwd": None},
                )
                multiple_res.append(res)

        [res.get() for res in multiple_res]


def synth_func(dir_str):
    navigate_dir_and_run(dir_str, config_file_name)


if __name__ == "__main__":
    run_for_dir_from_cli(workdir, synth_func)
