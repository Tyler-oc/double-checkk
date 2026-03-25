import os
import re

SOURCE_DIR = "./acsl-by-example"
OUTPUT_DIR = "./benchmarks/acsl_by_example"

# These keywords usually indicate "meta-code" that isn't a standalone function
IGNORE_KEYWORDS = [
    "axiom",
    "lemma",
    "property",
    "spec",
    "functional",
    "predicate",
    "logic",
    "invariant",
    "test",
]


def clean_c_code(code: str) -> str:
    # 1. Remove ACSL annotations
    code = re.sub(r"/\*@.*?\*/", "", code, flags=re.DOTALL)
    code = re.sub(r"//@.*", "", code)

    # 2. Remove local includes (#include "...") but keep standard ones (<...>)
    code = re.sub(r'^[ \t]*#include[ \t]+".*?".*$', "", code, flags=re.MULTILINE)

    # 3. HEALER: Some files use 'size_type' or 'value_type'.
    # Let's inject standard typedefs so Frama-C doesn't crash on them.
    prefix = "#include <stddef.h>\n#include <stdbool.h>\ntypedef size_t size_type;\ntypedef int value_type;\n\n"

    code = re.sub(r"\n\s*\n\s*\n", "\n\n", code)
    return prefix + code.strip()


def main():
    if not os.path.exists(SOURCE_DIR):
        return
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    processed_count = 0

    for root, dirs, files in os.walk(SOURCE_DIR):
        for file in files:
            if not file.endswith(".c"):
                continue

            # SKIP metadata, axioms, and lemmas
            if any(key in file.lower() for key in IGNORE_KEYWORDS) or any(
                key in root.lower() for key in IGNORE_KEYWORDS
            ):
                continue

            source_path = os.path.join(root, file)
            with open(source_path, "r", encoding="utf-8", errors="ignore") as f:
                content = f.read()

            clean_content = clean_c_code(content)

            # Ensure it's a real function implementation
            if "{" not in clean_content or len(clean_content) < 100:
                continue

            new_filename = f"{os.path.basename(root)}_{file}"
            with open(
                os.path.join(OUTPUT_DIR, new_filename), "w", encoding="utf-8"
            ) as f:
                f.write(clean_content)
            processed_count += 1

    print(f"✅ Extracted {processed_count} High-Quality benchmark files.")


if __name__ == "__main__":
    main()
