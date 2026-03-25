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
SV_COMP_HEALER = r"""
#include <stddef.h>
#include <stdlib.h>
#include <stdbool.h>

/*@ assigns \nothing; */
extern void abort(void);

/*@ assigns \nothing; */
extern void __VERIFIER_error(void);

/*@ assigns \nothing; */
extern void __VERIFIER_assume(int);

/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);

/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint(void);

/*@ assigns \nothing; */
extern long __VERIFIER_nondet_long(void);

/*@ assigns \nothing; */
extern unsigned long __VERIFIER_nondet_ulong(void);

/*@ assigns \nothing; */
extern short __VERIFIER_nondet_short(void);

/*@ assigns \nothing; */
extern unsigned short __VERIFIER_nondet_ushort(void);

/*@ assigns \nothing; */
extern char __VERIFIER_nondet_char(void);

/*@ assigns \nothing; */
extern unsigned char __VERIFIER_nondet_uchar(void);

/*@ assigns \nothing; */
extern _Bool __VERIFIER_nondet_bool(void);

/*@ requires \true; assigns \nothing; */
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
        ERROR: __VERIFIER_error();
    }
}
"""


def strip_svcomp_native_decls(code: str) -> str:
    """Remove duplicate __VERIFIER_* declarations and definitions from original SV-COMP source.

    SV-COMP files often re-declare or re-define these symbols inline after the healer block
    is prepended, causing duplicate-symbol errors and missing contracts in Frama-C.
    We strip them here so only the contracted versions from SV_COMP_HEALER survive.
    """
    # Strip #include <assert.h> — we provide our own abort stub
    code = re.sub(r"^\s*#include\s*<assert\.h>\s*$", "", code, flags=re.MULTILINE)

    # Strip bare "extern void abort(void);" re-declarations (healer provides the contracted one)
    code = re.sub(
        r"^\s*extern\s+void\s+abort\s*\(\s*void\s*\)\s*;\s*$",
        "",
        code,
        flags=re.MULTILINE,
    )

    # Strip reach_error() function definitions (single or multi-line, up to 2 brace levels)
    code = re.sub(
        r"\bvoid\s+reach_error\s*\(\s*\)\s*\{(?:[^{}]|\{[^{}]*\})*\}",
        "",
        code,
    )

    # Strip __VERIFIER_assert function definitions — healer provides a contracted version.
    # Pattern handles up to 3 levels of nested braces:
    #   e.g. { if(!(cond)) { ERROR: { reach_error(); abort(); } } }
    code = re.sub(
        r"\bvoid\s+__VERIFIER_assert\s*\([^)]*\)\s*"
        r"\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\}",
        "",
        code,
    )

    # Strip any bare extern __VERIFIER_* re-declarations (contracted versions are in the healer)
    code = re.sub(
        r"^\s*extern\s+\S+\s+__VERIFIER_\w+\s*\([^)]*\)\s*;\s*$",
        "",
        code,
        flags=re.MULTILINE,
    )

    return code


def clean_svcomp_code(code: str) -> str:
    # 1. Remove local SV-COMP headers if they exist
    code = re.sub(r'^[ \t]*#include[ \t]+".*?".*$', "", code, flags=re.MULTILINE)

    # 2. Strip duplicate __VERIFIER_* declarations and definitions from the original source
    code = strip_svcomp_native_decls(code)

    # 3. Inject the SV-COMP standard library mocks with ACSL contracts
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
