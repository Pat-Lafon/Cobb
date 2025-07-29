import subprocess
import os
import re
from pathlib import Path
# cmd : dune exec frequify -- -f [freq] -o [out] [dir]

in_dir_str = "./underapproximation_type/data/validation/"
out_dir_str = "../Cobb_PBT/bin/"

folder_names = {
    "completetree":"complete_tree",
    "depth_bst":"bsts",
    "depthtree":"depth_tree",
    "duplicatelist":"duplicate_list",
    "even_list":"even_list",
    "rbtree":"red_black_tree",
    "sizedlist":"sized_list",
    "sortedlist":"sorted_list",
    "uniquelist":"unique_list",
}

in_dir = Path(in_dir_str)
assert in_dir.is_dir()

# prog*.ml
for d in (os.listdir(in_dir)):
    gen_d = f"{in_dir}/{d}"
    match = re.search(r"(?:_excess)|(?:_imprecise)|(?:_[123]){1}|(?:_size)|(?:proofs)$", d)

    if (os.path.isdir(gen_d) and not match):
        is_stlc = re.search(r"stlc", d)
        if not (is_stlc):
            for f in os.listdir(gen_d):
                match = re.search(r"^prog[0-9]+\.ml.syn$", f)
                if match: 
                    in_file = f"{gen_d}/{f}"
                    base, ext, nothing = f.partition(".ml")
                    if d in folder_names:
                        out_file = f"{out_dir_str}{folder_names[d]}/{base}_syn{ext}"
                    else:
                        out_file = f"{out_dir_str}{d}/{base}_syn{ext}"
                    
                    print(f"i = {in_file}   o = {out_file}")

                    if d == "rbtree":
                        cmd = f"dune exec frequify -- -f unif_gen -o {out_file} {in_file}".split(" ")
                    else:
                        cmd = f"dune exec frequify -- -f freq_gen -o {out_file} {in_file}".split(" ")
                    subprocess.run(cmd)
            
