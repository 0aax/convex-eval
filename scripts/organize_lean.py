import json
import os
import os.path as osp
import pathlib
from typing import List

def formal_statements_from_file(lean_paths: List[str], save_path: str) -> None:
    """
    Save formal statements into a .json file.
    """
    organized_lean = []

    for lean_path in lean_paths:
        print("Reading file", lean_path)
        with open(lean_path, "r", encoding="utf-8") as f:
            lean_content = f.read()
            blocks = lean_content.split("\n\n")
            for block in blocks:
                if block[:2] == "--": continue  # skip commented out lines
                if "lemma" in block:
                    lemma_name = block.split("\n")[1].split(" ")[1]
                    comment = block.split("\n")[0]
                    commentless_block = "\n".join(block.split("\n")[1:])
                    example = {
                        "lean_tag": lemma_name,
                        "comment": comment,
                        "content": commentless_block
                    }
                    
                    organized_lean.append(example)
    
    organized_lean.sort(key=(lambda v: v["lean_tag"]))
    with open(save_path, "w", encoding="utf-8") as f:
        json.dump(organized_lean, f, indent=4, ensure_ascii=False)

if __name__ == "__main__":
    os.chdir("../")
    save_dir = osp.join(os.getcwd(), "dataset")
    pathlib.Path(save_dir).mkdir(exist_ok=True, parents=True)

    save_path = osp.join(save_dir, "lean_formalizations.json")
    lean_paths = [
        osp.join(os.getcwd(), "ConvexEval", "CAMA_chap_3.lean"),
        osp.join(os.getcwd(), "ConvexEval", "FCA_chap_B.lean"),
        osp.join(os.getcwd(), "ConvexEval", "FCA_chap_C.lean"),
        osp.join(os.getcwd(), "ConvexEval", "FCA_chap_D.lean"),
        osp.join(os.getcwd(), "ConvexEval", "FCA_chap_E.lean")
    ]
    formal_statements_from_file(lean_paths, save_path)
