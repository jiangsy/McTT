# usage: python checkall.py .
import os
import re
import sys
import subprocess
from pathlib import Path

COQ_ID = r"[A-Za-z_][A-Za-z0-9_']*"
eq_axiom = "Eqdep.Eq_rect_eq.eq_rect_eq"

def insert_debug_blocks_in_file(file_path: Path, root_dir: Path):
    content = file_path.read_text(encoding='utf-8')
    decl_pattern = re.compile(rf'^\s*(Lemma|Theorem|Corollary)\s+({COQ_ID})', re.MULTILINE)
    matches = list(decl_pattern.finditer(content))

    rel_path = f"./{file_path.relative_to(root_dir)}"

    for match in reversed(matches):
        name = match.group(2)
        start_pos = match.end()

        qed_pattern = re.compile(r'^\s*(Qed\.|Defined\.|Admitted\.)', re.MULTILINE)
        qed_match = qed_pattern.search(content, pos=start_pos)

        if qed_match:
            insert_pos = qed_match.end()
            marker = f"{rel_path} - {name}"
            snippet = (
                f'\nGoal True. idtac "<<<{marker}>>>". Abort.\n'
                f'Print Assumptions {name}.'
            )
            content = content[:insert_pos] + snippet + content[insert_pos:]

    file_path.write_text(content, encoding='utf-8')

def find_all_v_files(directory: Path) -> list:
    return sorted([f for f in directory.rglob("*.v")])

def run_make_and_capture_log(root: Path) -> Path:
    log_file = root / "make_output.log"
    try:
        env = os.environ.copy()
        # we need a sequential check so that outputs match the lemma names
        env["J"] = "1"  
        env["COQFLAGS"] = "-async-proofs off"
        env["COQFLAGS"] = "-async-proofs-j 0"
        result = subprocess.run(["make"], cwd=root, check=False, capture_output=True, text=True)
        output = result.stdout + "\n--- STDERR ---\n" + result.stderr
        print("🧱 `make` finished. Log captured.")
    except Exception as e:
        print(f"❌ Error running `make`: {e}")
        sys.exit(1)

    log_file.write_text(output, encoding='utf-8')
    return log_file

def extract_names_with_eq_rect(log_file: Path) -> list:
    lines = log_file.read_text(encoding='utf-8').splitlines()
    affected = []

    current_name = None
    assumptions_block = []
    in_assumptions = False

    for line in lines:
        stripped = line.strip()

        # Match: <<<./path/to/file.v - lemma_name>>>
        marker_match = re.match(r'^<<<(.+?) - (' + COQ_ID + r')>>>$', stripped)
        if marker_match:
            if current_name and any(eq_axiom in l for l in assumptions_block):
                affected.append(current_name)
            path = marker_match.group(1)
            lemma = marker_match.group(2)
            current_name = f"{path} - {lemma}"
            assumptions_block = []
            in_assumptions = False
            continue

        if stripped.startswith("Axioms:"):
            in_assumptions = True
            continue

        if in_assumptions:
            if re.match(rf"^{COQ_ID}$", stripped):
                in_assumptions = False
            else:
                assumptions_block.append(stripped)

    # Final block
    if current_name and any(eq_axiom in l for l in assumptions_block):
        affected.append(current_name)

    return affected

def main():
    if len(sys.argv) != 2:
        print("Usage: python track_eq_rect_make.py <directory>")
        sys.exit(1)

    root_dir = Path(sys.argv[1]).resolve()
    if not root_dir.is_dir():
        print("❌ Error: not a directory.")
        sys.exit(1)

    print(f"📂 Inserting debug statements into all .v files under: {root_dir}")
    v_files = find_all_v_files(root_dir)
    for f in v_files:
        insert_debug_blocks_in_file(f, root_dir)

    print(f"\n🔧 Running `make` inside: {root_dir}")
    log_path = run_make_and_capture_log(root_dir)

    print("🔍 Parsing make output for eq_rect_eq usage...")
    affected = extract_names_with_eq_rect(log_path)

    print(f"\n📌 Lemmas/theorems using `{eq_axiom}`:")
    if affected:
        for name in affected:
            print(f"- {name}")
    else:
        print("None found.")

if __name__ == "__main__":
    main()