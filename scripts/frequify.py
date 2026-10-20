import subprocess
import os
import re
import sys
from pathlib import Path
# cmd : dune exec frequify -- -f [freq] -o [out] -config [meta-config] [file]

in_dir = Path(__file__).resolve().parents[2] / "integration_tests"
working_dir = Path(__file__).resolve().parent.parent / "underapproximation_type"

folder_names = {
    "complete_tree": "complete_tree",
    "depth_bst": "bst",
    "depth_tree": "depth_tree",
    "duplicate_list": "duplicate_list",
    "even_list": "even_list",
    "rbtree": "red_black_tree",
    "sizedlist": "sized_list",
    "sortedlist": "sorted_list",
    "uniquelist": "unique_list",
}

t_pattern = r"true"
f_pattern = r"false"

if len(sys.argv) != 2:
    sys.exit(f"usage: {sys.argv[0]} <output-dir>")
out_dir = Path(sys.argv[1]).resolve()

for d in sorted(folder_names):
    gen_d = in_dir / d
    for f in sorted(os.listdir(gen_d)):
        match = re.search(r"_(prog[0-9]+)\.ml\.syn$", f)
        if not match:
            continue
        in_file = gen_d / f
        out_file = out_dir / folder_names[d] / f"{match.group(1)}_syn.ml"
        out_file.parent.mkdir(parents=True, exist_ok=True)

        freq = "unif_gen" if d == "rbtree" else "freq_gen"
        cmd = ["dune", "exec", "frequify", "--", "-f", freq, "-o", str(out_file),
               "-config", str(gen_d / "meta-config.json"), str(in_file)]

        # frequify parses the boolean literals capitalized; the .syn file is
        # rewritten for the call and restored afterwards.
        original = in_file.read_text()
        in_file.write_text(re.sub(f_pattern, "False", re.sub(t_pattern, "True", original)))
        try:
            print(" ".join(cmd))
            subprocess.run(cmd, cwd=working_dir, check=True)
        finally:
            in_file.write_text(original)
