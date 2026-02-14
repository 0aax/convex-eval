import json
import os
import os.path as osp
import pathlib
import re
from typing import Set

def get_statements_from_latex(latex_path : str, tags: Set[str]) -> None:
    """
    Gets statements and proofs (optional) from latex file.
    """
    tag_regex_patterns = [
        r'(\\begin\{{tag}\}(.*?)\\end\{{tag}\})\s*(?:\\begin{proof}.*?\\end{proof})?'.format(tag=tag)
        for tag in list(tags)
    ]

    statements_organized = []

    with open(latex_path, "r") as f:
        latex_text = f.read()
        for pattern in tag_regex_patterns:
            matches = re.findall(pattern, latex_text, re.DOTALL)