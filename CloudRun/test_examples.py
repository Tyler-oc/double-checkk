import json
import re
import subprocess
import tempfile
import os
import time

# Terminal colors for pretty output
GREEN = "\033[92m"
RED = "\033[91m"
YELLOW = "\033[93m"
RESET = "\033[0m"


def extract_code(example_text):
    """Extracts the C code from within the [[[ ]]] brackets."""
    match = re.search(r"\[\[\[(.*?)\]\]\]", example_text, re.DOTALL)
    if match:
        return match.group(1).strip()
    return None


def run_frama_c(c_code, timeout_sec=30):
    """Writes code to a temp file and runs Frama-C WP."""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".c", delete=False) as tmp:
        tmp.write(c_code)
        tmp_path = tmp.name

    # Standard command matching your frama_c.py setup
    cmd = ["frama-c", "-quiet", "-wp", "-wp-rte", "-wp-prover", "z3", tmp_path]

    try:
        t0 = time.time()
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout_sec
        )
        dur = time.time() - t0

        is_success = result.returncode == 0
        output = (result.stdout or "") + "\n" + (result.stderr or "")

    except subprocess.TimeoutExpired:
        is_success = False
        output = "Frama-C execution timed out."
        dur = timeout_sec
    finally:
        # Always clean up the temp file
        if os.path.exists(tmp_path):
            os.remove(tmp_path)

    return is_success, output, dur


def main():
    json_path = "examples.json"
    if not os.path.exists(json_path):
        print(f"{RED}Error: {json_path} not found in the current directory.{RESET}")
        return

    with open(json_path, "r") as f:
        data = json.load(f)

    total_run = 0
    total_passed = 0

    print("Starting Frama-C Example Validation Suite...\n")

    for category, examples in data.items():
        print(f"=== {category} ===")

        for ex in examples:
            # Extract the name (e.g., "Example 1 (Clamp Range)")
            name_match = re.match(r"(Example \d+ \([^)]+\))", ex)
            name = name_match.group(1) if name_match else "Unknown Example"

            code = extract_code(ex)

            # Handle the intentional failure cases
            if code == "!!i give up!!":
                print(
                    f"  {YELLOW}[SKIP]{RESET} {name} (Expected Unverifiable Fallback)"
                )
                continue

            if not code:
                print(f"  {RED}[ERROR]{RESET} {name} - No [[[ ]]] block found.")
                continue

            total_run += 1
            success, output, duration = run_frama_c(code)

            if success:
                print(f"  {GREEN}[PASS]{RESET} {name} ({duration:.2f}s)")
                total_passed += 1
            else:
                print(f"  {RED}[FAIL]{RESET} {name} ({duration:.2f}s)")
                # Print the first few lines of the error to help debug
                error_lines = [line for line in output.split("\n") if line.strip()][:5]
                for line in error_lines:
                    print(f"         {line}")

        print("")  # Blank line between categories

    # Final Summary
    print("-" * 40)
    if total_passed == total_run and total_run > 0:
        print(f"{GREEN}SUMMARY: {total_passed}/{total_run} Examples Passed!{RESET}")
    else:
        print(f"{RED}SUMMARY: {total_passed}/{total_run} Examples Passed.{RESET}")
        print(
            "Review the failed examples above. Frama-C may require specific standard library flags."
        )


if __name__ == "__main__":
    main()
