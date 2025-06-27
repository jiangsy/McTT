import re
import sys
from pathlib import Path

COQ_ID = r"[A-Za-z_][A-Za-z0-9_']*"
expected_axiom = ["functional_extensionality_dep"]

def check_assumptions(log_file: Path):
    lines = log_file.read_text(encoding='utf-8').splitlines()

    expecteds = []
    unexpecteds = []
    current_name = None

    for line in lines:
        stripped = line.strip()

        # Match: <<<./path/to/file.v - lemma_name>>>
        marker_match = re.match(r'^<<<(.+?) - (' + COQ_ID + r')>>>$', stripped)
        if marker_match:
            path = marker_match.group(1)
            lemma = marker_match.group(2)
            current_name = f"{lemma}"
            continue

        axiom_name_match = re.match(r'^(.*) :$', stripped)
        if axiom_name_match:
            axiom_name = axiom_name_match.group(1)
            if axiom_name in expected_axiom and current_name is not None:
                expecteds.append((current_name, axiom_name))
            if axiom_name not in expected_axiom and current_name is not None:
                unexpecteds.append((current_name, axiom_name))
            continue

    return expecteds, unexpecteds

def main():
    if len(sys.argv) != 2:
        print("Usage: python check_assumptions.py <log_file>")
        sys.exit(1)

    log_path = Path(sys.argv[1]).resolve()

    expecteds, unexpecteds = check_assumptions(log_path)
    print("Axioms usage:\n(due to coq's asynchronous checking, the usage may match up to the wrong theorem. However, the existence of the usage is 100% accurate)\n---------------------------------------------------------------------------------------")
    print("Expected:")
    for (thm_name, axiom_name) in expecteds:
        print(f"({thm_name}, {axiom_name})")
    print("\nUnexpected:")
    for (thm_name, axiom_name) in unexpecteds:
        print(f"({thm_name}, {axiom_name})")

    if unexpecteds:
        sys.exit(1)
    return 0

if __name__ == "__main__":
    main()
