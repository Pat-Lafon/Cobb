import sys
import argparse
import os
import subprocess
import shutil
import locale
import re
from pathlib import Path

cmd_prefix = ["dune", "exec", "--no-buffer", "--", "bin/main.exe", "subtype-check"]
config_file = "meta-config.json"
workdir = "underapproximation_type"
verbose = True

# Set up the local environment to avoid the global lock
my_env = os.environ.copy()
my_env["DUNE_CONFIG__GLOBAL_LOCK"] = "disabled"


def invoc_cmd(verbose, cmd, output_file, cwd=None):
    if output_file is not None:
        # print("{}:{}".format(output_file, type(output_file)))
        if verbose:
            print(" ".join(cmd + [">>", output_file]))
        with open(output_file, "a+") as ofile:
            try:
                subprocess.run(cmd, cwd=cwd, env=my_env, stdout=ofile)
            except subprocess.CalledProcessError as e:
                print(e.output)
                raise e
    else:
        if verbose:
            print(" ".join(cmd))
        try:
            p = subprocess.run(cmd, cwd, env=my_env, capture_output=True, text=True)
            if "Result: true" not in p.stdout:
                print("Error: subtype-check failed")
                print(cmd)
                raise Exception("subtype-check failed")
        except subprocess.CalledProcessError as e:
            print(e.output)
            raise e


def run_synthesis_aux(dir_str, f):
    cmd = cmd_prefix + [config_file, dir_str + "/" + f]

    invoc_cmd(verbose, cmd, None, cwd=None)


def run_synthesis(dir_str):
    meta_config_file = config_file
    if not (os.path.exists(meta_config_file)):
        print("Error: meta-config.json not found in {}".format(dir_str))
        exit(1)
    else:
        from multiprocessing import Pool

        pool = Pool()

        multiple_res = []
        for filename in os.listdir(dir_str):
            res = pool.apply_async(run_synthesis_aux, args=(dir_str, filename))
            multiple_res.append(res)

        [res.get() for res in multiple_res]


if __name__ == "__main__":
    dir_str = sys.argv[1]

    directory = Path(dir_str)
    assert directory.is_dir()

    working_dir = Path(workdir)
    assert working_dir.is_dir()

    assert directory.is_relative_to(working_dir)
    os.chdir(working_dir)
    directory = os.path.relpath(directory, working_dir)

    run_synthesis(directory)
