import os
import subprocess

my_env = os.environ.copy()
# "DUNE_CONFIG__GLOBAL_LOCK=disabled",
my_env["DUNE_CONFIG__GLOBAL_LOCK"] = "disabled"


def invoc_cmd(verbose, cmd, output_file=None, cwd=None):
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
            res = subprocess.run(cmd, cwd=cwd, env=my_env)
            if res.returncode != 0:
                raise subprocess.CalledProcessError(res.returncode, cmd)
        except subprocess.CalledProcessError as e:
            print(e.output)
            raise e
