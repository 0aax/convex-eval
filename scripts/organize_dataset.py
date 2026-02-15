import json
import os
import os.path as osp
import pathlib
import re
from typing import Set, List

def get_statements_from_latex(latex_paths : List[str], formalizations_path: str,
                              save_path: str, save_with_lean_path: str,
                              tags: Set[str]) -> None:
    """
    Gets statements and proofs (optional) from latex files.
    """
    tag_regex_patterns = []
    for tag in list(tags):
        pattern = re.compile(
            r'\\begin{' + tag + r'}(?:\[(.*?)\])?'
            r'\s*(?:\\label\{(.*?)\})?'
            r'\s*(?:\\lean\{(.*?)\})?'
            r'(.*?)'
            r'\\end{' + tag + r'}\s*'
            r'(?:\\begin{proof}(.*?)\\end{proof})?',
            re.DOTALL
        )
        tag_regex_patterns.append(pattern)

    statements_organized = []
    statements_with_lean_organized = []

    with open(formalizations_path, "r", encoding="utf-8") as f:
        lean_formalizations = json.load(f)
        lean_lookup = {
            example["lean_tag"]: example["content"] for example in lean_formalizations
        }

    for latex_path in latex_paths:
        print("Reading:", latex_path)
        with open(latex_path, "r", encoding="utf-8") as f:
            latex_text = f.read()
            for pattern in tag_regex_patterns:
                matches = re.findall(pattern, latex_text)

                for i, (title, label, lean_tag, statement, proof_content) in enumerate(matches):
                    example = {"statement": statement.strip()}
                    if title: example["title"] = title.strip()
                    else: example["title"] = ""

                    if label: example["label"] = label
                    else: example["label"] = "no-label"

                    if lean_tag:
                        example["lean_tag"] = lean_tag.split(",")
                        example["lean_formalization"] = lean_lookup[lean_tag.split(",")[0]]    # TODO: handle multiple multi-part formalizations
                    else: example["lean_tag"] = "no-lean-tag"

                    if proof_content: example["proof"] = proof_content.strip()
                    else: example["proof"] = ""
                
                    statements_organized.append(example)

                    if lean_tag: statements_with_lean_organized.append(example)

    statements_organized.sort(key=(lambda v: v["label"].split(":")[-1]))
    statements_with_lean_organized.sort(key=(lambda v: v["label"].split(":")[-1]))
    
    with open(save_path, "w", encoding="utf-8") as f:
        json.dump(statements_organized, f, indent=4, ensure_ascii=False)
    
    with open(save_with_lean_path, "w", encoding="utf-8") as f:
        json.dump(statements_with_lean_organized, f, indent=4, ensure_ascii=False)

if __name__ == "__main__":
    os.chdir("../")
    save_dir = osp.join(os.getcwd(), "dataset")
    pathlib.Path(save_dir).mkdir(exist_ok=True, parents=True)

    save_path = osp.join(save_dir, "dataset.json")
    save_with_lean_path = osp.join(save_dir, "dataset_with_lean.json")

    CAMA_paths = [osp.join(os.getcwd(), "blueprint", "src", "books", "CAMA", "chapter_3", f"section_{i}.tex") for i in range(1, 6)]
    FCA_chapB_paths = [osp.join(os.getcwd(), "blueprint", "src", "books", "FCA", "chapter_B", f"section_{i}.tex") for i in range(1, 5)]
    FCA_chapC_paths = [osp.join(os.getcwd(), "blueprint", "src", "books", "FCA", "chapter_C", f"section_{i}.tex") for i in range(1, 4)]
    FCA_chapD_paths = [osp.join(os.getcwd(), "blueprint", "src", "books", "FCA", "chapter_D", f"section_{i}.tex") for i in range(1, 7)]
    FCA_chapE_paths = [osp.join(os.getcwd(), "blueprint", "src", "books", "FCA", "chapter_E", f"section_{i}.tex") for i in range(1, 5)]

    formalization_path = osp.join(os.getcwd(), "dataset", "lean_formalizations.json")

    latex_paths = CAMA_paths + FCA_chapB_paths + FCA_chapC_paths + FCA_chapD_paths + FCA_chapE_paths

    get_statements_from_latex(latex_paths, formalization_path, save_path, save_with_lean_path, tags={"proposition", "lemma", "corollary", "theorem"})