import re
import sys
from pathlib import Path

# TODO: checking the name only may not be suffient,
# as one could redefine `Axiom functional_extensionality_dep : False`
# to prove anything and bypass the check
# but let us just use this for CI now
expected_axiom = ["functional_extensionality_dep"]

def check_assumptions(log_file: Path):
    lines = log_file.read_text(encoding='utf-8').splitlines()

    expecteds = []
    unexpecteds = []
    lemma_name = None

    for line in lines:
        stripped = line.strip()

        # Match: <<<./path/to/file.v - lemma_name>>>
        marker_match = re.match(r'^<<<(.+?) - (.*)>>>$', stripped)
        if marker_match:
            path = marker_match.group(1)
            lemma_name = marker_match.group(2)
            continue

        axiom_name_match = re.match(r'^(.*) :$', stripped)
        if axiom_name_match:
            axiom_name = axiom_name_match.group(1)
            if axiom_name in expected_axiom and lemma_name is not None:
                expecteds.append((lemma_name, axiom_name))
            elif axiom_name not in expected_axiom and lemma_name is not None:
                unexpecteds.append((lemma_name, axiom_name))
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
