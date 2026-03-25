import os
import re

# --- CONFIGURATION ---
SOURCE_DIR = "./sv-benchmarks/c"
OUTPUT_DIR = "./benchmarks/sv_comp"

# We only want to target specific, high-value benchmark categories
# to avoid extracting 10,000+ files.
TARGET_FOLDERS = ["array-examples", "bitvector", "memsafety"]
MAX_FILES_TO_EXTRACT = 50

# SV-COMP files use custom verification functions.
# We inject these stubs so Frama-C doesn't crash with "undeclared function" errors.
SV_COMP_HEALER = """
#include <stddef.h>
extern void __VERIFIER_error(void);
extern void __VERIFIER_assume(int);
extern int __VERIFIER_nondet_int(void);
extern unsigned int __VERIFIER_nondet_uint(void);
extern _Bool __VERIFIER_nondet_bool(void);
void __VERIFIER_assert(int cond) { if (!(cond)) { ERROR: __VERIFIER_error(); } }

"""


def clean_svcomp_code(code: str) -> str:
    # 1. Remove local SV-COMP headers if they exist
    code = re.sub(r'^[ \t]*#include[ \t]+".*?".*$', "", code, flags=re.MULTILINE)

    # 2. Inject the SV-COMP standard library mocks
    return SV_COMP_HEALER + code.strip()


def main():
    if not os.path.exists(SOURCE_DIR):
        print(f"Error: Could not find {SOURCE_DIR}. Did the clone finish?")
        return

    os.makedirs(OUTPUT_DIR, exist_ok=True)
    processed_count = 0

    print("Extracting and healing SV-COMP C files...")

    for root, dirs, files in os.walk(SOURCE_DIR):
        # Only process files if they are in our targeted folders
        if not any(folder in root for folder in TARGET_FOLDERS):
            continue

        for file in files:
            if processed_count >= MAX_FILES_TO_EXTRACT:
                break

            if file.endswith(".c"):
                source_path = os.path.join(root, file)

                try:
                    with open(source_path, "r", encoding="utf-8", errors="ignore") as f:
                        content = f.read()
                except Exception as e:
                    continue

                # SV-COMP files often contain intentionally broken code to test if
                # tools can catch the bug. For your benchmark, we want the "true"
                # files (the ones that are mathematically provable).
                if "false-unreach-call" in file or "false-valid-deref" in file:
                    continue

                clean_content = clean_svcomp_code(content)

                # Ensure it has a main function or significant logic
                if "main" not in clean_content or len(clean_content) < 100:
                    continue

                parent_folder = os.path.basename(root)
                new_filename = f"{parent_folder}_{file}"
                output_path = os.path.join(OUTPUT_DIR, new_filename)

                with open(output_path, "w", encoding="utf-8") as f:
                    f.write(clean_content)

                processed_count += 1

        if processed_count >= MAX_FILES_TO_EXTRACT:
            break

    print(
        f"✅ Success! Extracted and healed {processed_count} SV-COMP files into {OUTPUT_DIR}"
    )


if __name__ == "__main__":
    main()
