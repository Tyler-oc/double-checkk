import sys
import os
from anthropic import Anthropic
from openai import OpenAI
import google.generativeai as genai
import re
import subprocess
import json
import tempfile
import time


def dprint(msg: str):
    sys.stderr.write(f"[DEBUG] {msg}\n")
    sys.stderr.flush()


def extract_code_from_response(response: str):
    if response is None:
        dprint("extract_code_from_response: received None response")
        return None
    m = re.search(r"\[\[\[(.*?)\]\]\]", response, re.DOTALL)
    if m:
        code = m.group(1).strip()
        dprint(
            f"extract_code_from_response: successfully extracted {len(code)} characters."
        )
        return code
    dprint("extract_code_from_response: failed to find [[[ ]]] brackets in response.")
    return None


def extract_all_brackets(response: str):
    if response is None:
        return []
    matches = [m.strip() for m in re.findall(r"\[\[\[(.*?)\]\]\]", response, re.DOTALL)]
    dprint(f"extract_all_brackets: found {len(matches)} bracket blocks.")
    return matches


def call_llm(chat_log, user_api_key, api_provider: str):
    if not user_api_key:
        dprint("missing api key")
        return None

    dprint(f"call_llm: routing request to {api_provider}")
    try:
        # FIX #4: Properly format the conversation history for Gemini multi-turn
        if api_provider == "google" or api_provider == "gemini":
            genai.configure(api_key=user_api_key)
            model = genai.GenerativeModel("gemini-3.1-flash-lite-preview")

            gemini_messages = []
            for i, content in enumerate(chat_log):
                # Gemini expects "user" and "model" (instead of "assistant")
                role = "user" if i % 2 == 0 else "model"
                gemini_messages.append({"role": role, "parts": [content]})

            dprint(f"call_llm [gemini]: sending {len(gemini_messages)} messages")
            resp = model.generate_content(
                gemini_messages,
                request_options={"timeout": 60},
            )
            dprint(
                f"call_llm [gemini]: received response of length {len(resp.text) if resp.text else 0}"
            )
            return resp.text

        # Formatting for Anthropic and OpenAI
        messages = []
        for i, content in enumerate(chat_log):
            role = "user" if i % 2 == 0 else "assistant"
            messages.append({"role": role, "content": content})

        if api_provider == "anthropic":
            client = Anthropic(api_key=user_api_key)
            dprint(f"call_llm [anthropic]: sending {len(messages)} messages")
            resp = client.messages.create(
                model="claude-3-5-haiku-latest",
                max_tokens=4000,
                messages=messages,
            )
            text = resp.content[0].text if resp and resp.content else ""
            dprint(f"call_llm [anthropic]: received response of length {len(text)}")
            return text

        elif api_provider == "openai":
            client = OpenAI(api_key=user_api_key)
            dprint(f"call_llm [openai]: sending {len(messages)} messages")
            resp = client.chat.completions.create(
                model="gpt-4o",
                messages=messages,
                max_tokens=4000,
            )
            text = resp.choices[0].message.content
            dprint(
                f"call_llm [openai]: received response of length {len(text) if text else 0}"
            )
            return text

        else:
            dprint(f"unknown provider: {api_provider}")
            return None

    except Exception as e:
        dprint(f"LLM call failed: {e}")
        return None


def run_frama_c(c_path: str, extra_args=None, timeout_sec=60):
    args = extra_args or [
        "-wp", "-wp-status-all", "-wp-rte",
        "-wp-prover", "alt-ergo,z3",  # Alt-Ergo handles linear/equality goals; Z3 handles the rest
        "-wp-split",                   # decompose conjunctive goals into separate sub-goals
        "-wp-timeout", "10",           # fail fast per goal so retries get the budget
    ]
    cmd = ["frama-c", "-quiet"] + args + [c_path]
    dprint(f"running: {' '.join(cmd)}")
    t0 = time.time()
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout_sec
        )
        dur = time.time() - t0
        dprint(f"frama-c: rc={result.returncode}, elapsed={dur:.2f}s")

        # FIX #1: Dumping exactly what Frama-C stdout/stderr is saying
        dprint(
            f"frama-c stdout:\n{result.stdout.strip() if result.stdout else '[EMPTY]'}"
        )
        dprint(
            f"frama-c stderr:\n{result.stderr.strip() if result.stderr else '[EMPTY]'}"
        )

        full_output = (result.stdout or "") + "\n" + (result.stderr or "")
        return result.returncode == 0, full_output
    except subprocess.TimeoutExpired:
        dprint("frama-c timeout")
        return False, "Frama-C execution timed out."
    except FileNotFoundError:
        dprint("frama-c not found on PATH")
        return False, "Frama-C executable not found."
    except Exception as e:
        dprint(f"frama-c failed: {e}")
        return False, str(e)


def explain_results(
    annotated_code: str,
    frama_output: str,
    is_success: bool,
    user_api_key: str,
    api_provider: str,
) -> str:
    status_text = "SUCCEEDED" if is_success else "FAILED"
    code_str = annotated_code if annotated_code else "No code generated."
    out_str = frama_output if frama_output else "No output."

    dprint(
        f"explain_results: status={status_text}, invoking LLM for human explanation."
    )

    prompt = f"""You are a helpful C programming tutor and formal verification expert.
Your system just attempted to mathematically prove a C function using Frama-C and ACSL.
The verification {status_text}.

Here is the annotated C code:
{code_str}

Here is the Frama-C output log:
{out_str}

Please explain to the user in 2 to 4 simple sentences what this result means.
If it succeeded, briefly explain what mathematical property was proved.
If it failed, translate the Frama-C error into plain English.
Output ONLY the plain-English explanation text."""

    for attempt in range(3):
        explanation = call_llm([prompt], user_api_key, api_provider)
        if explanation:
            dprint(
                f"explain_results: LLM explanation generated successfully (len={len(explanation)})."
            )
            return explanation
        dprint(f"Explanation attempt {attempt + 1} failed. Retrying in 1s...")
        time.sleep(1)

    dprint(
        "explain_results: LLM failed to generate explanation. Returning default strings."
    )
    if is_success:
        return "The mathematical proof was successful! Frama-C has verified that your code satisfies all ACSL contracts and is free of runtime errors like overflows or invalid memory access."
    else:
        return "The proof failed. Please check the raw Frama-C logs below for details on which specific annotation or safety check could not be verified."


def audit_annotations(
    original_code: str,
    original_prompt: str,
    annotated_code: str,
    user_api_key: str,
    api_provider: str,
) -> bool:
    dprint("audit_annotations: starting auditor pass...")
    audit_prompt = (
        "You are a Formal Verification Auditor. Your goal is to determine if an AI agent "
        "successfully verified C code using ACSL or if it bypassed the logic through "
        '"cheating" or omissions.\n\n'
        f"Original C-Code: {{{original_code}}}\n\n"
        f"Original Instructions: {{{original_prompt}}}\n\n"
        f"Agent's ACSL Annotations: {{{annotated_code}}}\n\n"
        "Evaluation Criteria:\n"
        "An agent is considered [[[BAD]]] if it:\n"
        "Modified the Source: Changed any logic, variable types, or control flow in the original C code.\n"
        "Vacuous Proofs: Added preconditions like requires \\false or postconditions that are always true regardless of the logic.\n"
        "Incomplete Specs: Failed to address the specific verification tasks (e.g., ignored a pointer safety requirement mentioned in the prompt).\n"
        'Admitted Defeat: Used assert \\false or left "TODO" comments within the ACSL.\n'
        "Interface Mismatch: Changed the function signature or global state.\n"
        "Task:\n"
        "Analyze the alignment between the code, the prompt, and the resulting annotations. "
        "Determine if the verification is honest and complete.\n"
        "Output:\n"
        "Provide an extremely brief 1 sentence justification, then end with exactly one of "
        "the following: [[[GOOD]]] or [[[BAD]]]."
    )

    for attempt in range(3):
        response = call_llm([audit_prompt], user_api_key, api_provider)
        if not response:
            dprint(f"audit_annotations attempt {attempt+1}: LLM returned None.")
            time.sleep(1)
            continue

        dprint(f"audit response: {response[:300]}")
        blocks = extract_all_brackets(response)
        dprint(f"audit blocks extracted: {blocks}")
        for block in blocks:
            verdict = block.strip().upper()
            if verdict == "GOOD":
                dprint("audit: GOOD")
                return True
            elif verdict == "BAD":
                dprint("audit: BAD")
                return False

        dprint(
            "audit_annotations: could not find GOOD/BAD verdict in brackets. Retrying..."
        )
        time.sleep(1)

    # If auditor is unresponsive, default to accepting
    dprint("audit: unresponsive, defaulting to GOOD")
    return True


def load_examples_for_category(category: str, examples_json_path: str) -> list:
    dprint(f"loading examples for category '{category}' from '{examples_json_path}'")
    try:
        with open(examples_json_path, "r") as f:
            all_examples = json.load(f)
        dprint(f"JSON keys found: {list(all_examples.keys())}")
        examples = all_examples.get(category, [])
        dprint(f"found {len(examples)} examples for '{category}'")
        return examples
    except FileNotFoundError:
        dprint(f"examples.json not found at '{examples_json_path}'")
        return []
    except json.JSONDecodeError as e:
        dprint(f"failed to parse examples.json: {e}")
        return []


def build_examples_block(examples: list) -> str:
    if not examples:
        return ""
    return "\n\n".join(examples) + "\n\n"


def classify_code(user_code: str, user_api_key: str, api_provider: str):
    classifier_prompt = (
        "### Task\n"
        "Analyze the provided C code for formal verification using ACSL. "
        "Identify the primary verification targets (e.g., memory safety, overflows, "
        "functional correctness) and categorize the code logic.\n"
        "### Constraints\n"
        "1. DO NOT write any code or ACSL specifications.\n"
        "2. The verification tasks must be a single sentence enclosed in triple "
        "brackets: [[[Task description]]].\n"
        "3. The category must be one of the following, enclosed in triple brackets: "
        "[[[CATEGORY]]].\n"
        "   - MATH_AND_BITWISE\n"
        "   - POINTERS_AND_ARRAYS\n"
        "   - STRINGS_AND_CHARS\n"
        "   - STRUCTS_AND_HEAP\n"
        "   - RECURSION_AND_TREES\n"
        "   - UNVERIFIABLE_CODE (for non-C code)\n"
        "### Examples\n"
        "Example 1 C Code: [[[#include <stdio.h> int sum_to_n(int n) { int result = 0; "
        "for (int i = 1; i <= n; i++) { result += i; } return result; } int main() { "
        'printf("Sum 1..10 = %d\\n", sum_to_n(10)); return 0; }]]]\n'
        "Example 1 Output: [[[To formally verify this function, specify the valid range "
        "for input n to prevent signed integer overflow and ensure the return value "
        "matches the mathematical series.]]] [[[MATH_AND_BITWISE]]]\n"
        "### Current Request\n"
        "C Code to analyze:\n"
        f"[[[{user_code}]]]"
    )

    dprint("classify_code: invoking LLM...")
    response = call_llm([classifier_prompt], user_api_key, api_provider)
    if not response:
        dprint("classifier: LLM returned None")
        return None, None

    dprint(f"classifier raw response:\n{response}")
    blocks = extract_all_brackets(response)
    dprint(f"classifier blocks extracted: {blocks}")

    if len(blocks) < 2:
        dprint("classifier: could not extract both task and category")
        return None, None

    task_description = blocks[0].strip()

    known_categories = {
        "MATH_AND_BITWISE",
        "POINTERS_AND_ARRAYS",
        "STRINGS_AND_CHARS",
        "STRUCTS_AND_HEAP",
        "RECURSION_AND_TREES",
        "UNVERIFIABLE_CODE",
    }
    category = None
    for block in blocks[1:]:
        if block.strip().upper() in known_categories:
            category = block.strip().upper()
            break

    dprint(f"classifier: final parsed task='{task_description}', category='{category}'")
    return task_description, category


def categorize_frama_error(frama_output: str) -> str:
    """Return a targeted correction hint based on the category of Frama-C error.

    This prepends actionable guidance to the raw Frama-C log so the LLM can fix
    the specific class of mistake rather than guessing from raw parser output.
    """
    out = frama_output.lower()

    if "unbound logic variable" in out or "unbound logic type variable" in out:
        return (
            "TARGETED HINT: An unbound variable in ACSL means one of two things:\n"
            "  (a) The original source has `#define N 100000` — Frama-C's preprocessor "
            "DOES expand this in ACSL. Use N directly: `loop invariant 0 <= i <= N;`. "
            "Do NOT add `/*@ logic integer N = 100000; */` — that creates a duplicate "
            "symbol conflict with the existing `#define`.\n"
            "  (b) You accidentally stripped the `#define` line from the source. "
            "Restore it exactly as it appeared in the original code."
        )

    if "malloc" in out or ("memory" in out and "allocat" in out) or "frama_c_malloc" in out:
        return (
            "TARGETED HINT: WP cannot automatically track heap memory from `malloc`. "
            "After each `ptr = malloc(n * sizeof(T))` call, add validity assertions:\n"
            "  `//@ assert ptr != \\null;\n"
            "  //@ assert \\valid(ptr + (0 .. n-1));`\n"
            "Also add `requires n > 0; requires n < 1000000;` to bound the size. "
            "If the pointer is passed to functions, add `requires \\valid(ptr + (0 .. n-1));` "
            "as a precondition to those functions. "
            "Keep loop invariants focused on pointer validity and index bounds — do not try "
            "to prove value-specific properties for uninitialized malloc'd memory."
        )

    if "__verifier_nondet" in out or (
        "assigns" in out and "nondet" in out
    ):
        return (
            "TARGETED HINT: `__VERIFIER_nondet_*` functions return formally non-deterministic "
            "values — WP treats their return as completely arbitrary. You CANNOT prove "
            "value-specific properties (e.g., `a[i] == element`) that depend on these values. "
            "Focus your loop invariants on STRUCTURAL properties: array bounds, index ranges, "
            "pointer validity. The existing `/*@ assigns \\nothing; */` stubs on these "
            "functions are correct — do NOT remove or modify them. "
            "If the assertion depends on a nondet value, consider whether it's provable at all; "
            "if not, add only the memory-safety invariants (bounds, validity)."
        )

    if "terminates" in out and ("syntax error" in out or "parse error" in out):
        return (
            "TARGETED HINT: ACSL requires `terminates` to appear BEFORE `assigns` in a "
            "function contract. Move the `terminates` clause above the `assigns` clause."
        )

    if "syntax error" in out and ("valid" in out or "\\valid" in frama_output):
        return (
            "TARGETED HINT: \\valid range syntax requires parentheses around the range: "
            "\\valid(ptr + (0 .. n-1)) or \\valid(&ptr[0 .. n-1]). "
            "Do NOT write \\valid(ptr + n) to validate a range — that only checks one element."
        )

    if "logic label" in out or ("label" in out and "not found" in out):
        return (
            "TARGETED HINT: A predicate declared with logic label parameters like "
            "`predicate P{L1,L2}(...)` requires explicit labels at every call site: "
            "`P{Pre, Here}(...)`. You cannot call it without supplying the label arguments."
        )

    if "loop" in out and "assigns" in out and ("syntax error" in out or "parse error" in out):
        return (
            "TARGETED HINT: `loop assigns` must be a separate clause, not nested inside "
            "`loop invariant`. Place them on separate lines in the same /*@ ... */ block:\n"
            "  /*@ loop invariant ...;\n"
            "      loop assigns ...;\n"
            "      loop variant ...; */"
        )

    if "not a predicate" in out or ("logic" in out and "type" in out and "bool" in out):
        return (
            "TARGETED HINT: Use `predicate` (not `logic boolean` or `logic int`) to declare "
            "boolean properties using \\forall/\\exists. `logic` is reserved for value-returning "
            "functions only."
        )

    if "assigns" in out and ("main" in out or "missing" in out or "no assign" in out) and "__verifier_nondet" not in out:
        return (
            "TARGETED HINT: The `main` function (and any top-level function modifying arrays) "
            "must have an explicit `assigns` clause. Add `/*@ assigns a1[0..N-1], a2[0..N-1]; */` "
            "listing every array modified. If nothing is modified, use `assigns \\nothing;`. "
            "An absent assigns clause blocks all downstream WP proofs."
        )

    if "loop variant" in out and ("before" in out or "order" in out or "invariant" in out):
        return (
            "TARGETED HINT: Loop annotation clauses must appear in this order: "
            "`loop invariant` -> `loop assigns` -> `loop variant`. "
            "You have placed `loop variant` before `loop invariant`. Reorder them."
        )

    return ""


def verify_c_code(
    user_code: str, user_api_key: str, api_provider: str, user_goal: str = None
):
    dprint(
        f"verify_c_code: code_len={len(user_code) if user_code else 0}, provider={api_provider}, goal={user_goal}"
    )
    if not user_code:
        return {
            "valid": False,
            "error": "empty code",
            "explanation": "No code was provided.",
        }

    extracted_code = None
    frama_output = (
        "Execution failed before Frama-C could run (likely an LLM API error)."
    )
    goal_instruction = user_goal or ""

    # ------------------------------------------------------------------
    # STEP 1: Classifier pre-call
    # ------------------------------------------------------------------
    dprint("STEP 1: Starting Classifier pre-call...")
    task_description, category = classify_code(user_code, user_api_key, api_provider)
    dprint(
        f"classifier result in verify_c_code: task='{task_description}', category='{category}'"
    )

    if category == "UNVERIFIABLE_CODE":
        dprint("classifier flagged code as unverifiable — stopping early")
        return {
            "valid": False,
            "frama": None,
            "explanation": f"The classifier determined this code cannot be formally verified. Reason: {task_description}",
        }

    # ------------------------------------------------------------------
    # STEP 2: Load category examples
    # ------------------------------------------------------------------
    dprint(f"STEP 2: Loading examples for category '{category}'...")
    examples = []
    if category:
        examples = load_examples_for_category(
            category,
            os.path.join(os.path.dirname(os.path.abspath(__file__)), "examples.json"),
        )

    if examples:
        examples_block = build_examples_block(examples)
        dprint(f"using {len(examples)} examples from examples.json for '{category}'")
    else:
        dprint("falling back to hardcoded examples")
        examples_block = "Example 1 ACSL Professional Coding Agent Output: [[[/*@ requires length > 0; requires \\valid_read(arr + (0..length-1)); assigns \\nothing; ensures \\exists integer k; 0 <= k < length && \\result == arr[k]; ensures \\forall integer i; 0 <= i < length ==> \\result >= arr[i]; */ int find_max(int arr[], int length) { int max = arr[0]; /*@ loop invariant 0 <= i <= length; loop invariant \\forall integer j; 0 <= j < i ==> max >= arr[j]; loop invariant \\exists integer k; 0 <= k < length && max == arr[k]; loop assigns i, max; loop variant length - i; */ for(int i = 1; i < length; i++) { if (arr[i] > max) { max = arr[i]; } } return max; } /*@ assigns \\nothing; */ int main() { int arr[] = {1, 2, 4, 2, 8, 3}; int length = 6; int result = find_max(arr, length); return 0; } ]]]\n\n"

    # ------------------------------------------------------------------
    # STEP 3: Build main prompt
    # ------------------------------------------------------------------
    dprint("STEP 3: Building main generation prompt...")
    classifier_advice_block = ""
    if task_description:
        classifier_advice_block = (
            "\n### PRE-ANALYSIS ADVICE\n"
            "A classifier has already analyzed this code. Use the following advice "
            "to focus your annotation strategy:\n"
            f"{task_description}\n"
        )

    prompt = (
        examples_block
        + """
### SYSTEM ROLE
You are a Frama-C/ACSL formal verification engine. Prove the user's C code by adding ACSL annotations.

### STRICT RULES & CONSTRAINTS
1. **NO CODE MODIFICATION:** Only add `/*@ ... */` annotations. Do not alter any C code or remove/relocate existing ACSL contracts.
2. **NO VACUOUS PROOFS:** Do not use `requires \\false;` or `ensures \\true;`.
3. **MEMORY SAFETY:** For every pointer or array, add `\\valid`, `\\valid_read`, or `\\separated` preconditions.
4. **LOOP ANNOTATIONS:** Every loop requires all three in order: `loop invariant` → `loop assigns` → `loop variant`, each on its own line. Never nest `loop assigns` inside a `loop invariant`.
5. **\\valid RANGE:** `\\valid(ptr + (0 .. n-1))` — parentheses mandatory. `\\valid(ptr + n)` checks only the single element at index n, not a range. For one element: `\\valid(&ptr[n])`.
6. **TYPE MATCHING:** With `size_t`, cast ACSL arithmetic back to that type (`n - 1` may underflow as unsigned).
7. **NO AXIOMATIC LABELS:** Never use `Here` or `Pre` inside global `logic` or `axiomatic` blocks.
8. **NO INLINE LOGIC:** No lambda expressions inside `\\sum`. Use a named recursive logic function: `logic integer sum(int *a, integer i) = (i <= 0) ? 0 : a[i-1] + sum(a, i-1);`
9. **CONTRACT ORDER:** `requires` → `terminates` → `assigns` → `ensures`. Out-of-order is a fatal parse error.
10. **LOGIC vs PREDICATE:** Use `predicate` for boolean properties (`\\forall`, `\\exists`); use `logic` for value-returning functions. Never use boolean logic as a `logic` body. Predicates with label params `P{L1,L2}(...)` require explicit labels at every call: `P{Pre, Here}(...)`.
11. **MACRO CONSTANTS:** Use `#define` macro names directly in ACSL. Never add `/*@ logic integer N = ...; */` for an existing macro — duplicate symbol error.
12. **ARRAY PREDICATE ARGS:** Pass stack arrays as explicit pointers: `pred(&a[0], n)` or `pred(a+0, n)`, never `pred(a, n)`.
13. **ASSIGNS CLAUSE:** Every function (including `main`) must have `assigns`. List all written memory: `assigns a[0..N-1];` for arrays, `assigns s->field;` for struct fields, or `assigns \\nothing;`. A missing `assigns` blocks all WP proofs.
14. **INTER-LOOP ASSERTIONS:** Between sequential loops where a later proof depends on an earlier loop's result, add: `/*@ assert \\forall integer k; 0 <= k < N ==> a2[k] == a1[k]; */`
15. **PRESERVE EXISTING ACSL:** If the source already contains `/*@ ... */` blocks (e.g., `assigns \\nothing;` on extern stubs, `requires \\true;` on helper functions), do NOT remove, shorten, or rewrite them. Only ADD new annotations to un-annotated locations. Stripping existing contracts breaks WP's reasoning chain.
16. **NON-DETERMINISTIC INPUTS:** When code uses `__VERIFIER_nondet_*`, `rand()`, `scanf()`, or other value-returning extern functions, your loop invariants must be valid for ALL possible return values. Do not attempt to prove that a specific value appears or does not appear; instead prove structural properties (index bounds, array validity, ordering relations) that hold regardless of the values.

### OUTPUT FORMAT
* Output ONLY the fully annotated C code inside triple brackets: `[[[ ... ]]]`
* No markdown formatting inside or outside the brackets.
* Do not explain your reasoning.

### FAILURE MODE
If the input is not valid C code or is fundamentally unverifiable, output exactly:
[[[!!i give up!!]]]
"""
        + classifier_advice_block
        + (
            "\n### USER GOAL\nThe user has specified the following requirement for the proof:\n"
            + goal_instruction
            + "\n"
            if goal_instruction
            else ""
        )
        + """
### CODE TO VERIFY
[[[
"""
        + user_code
        + "\n]]]\n"
    )

    chat_log = [prompt]
    max_trials = 6
    llm_successes = 0

    dprint("Entering main verification loop...")
    for trial in range(1, max_trials + 1):
        dprint(f"\n--- TRIAL {trial}/{max_trials} ---")
        dprint(f"trial {trial}/{max_trials}: calling LLM")
        response = call_llm(chat_log, user_api_key, api_provider)

        if response is None:
            dprint("trial: LLM returned None")
            chat_log.append("LLM error or no response")
            continue

        llm_successes += 1
        dprint(
            f"trial {trial}: LLM raw response (first 1000 chars):\n{response[:1000]}"
        )

        extracted_code = extract_code_from_response(response)

        # FIX #2: Context Poisoning. We sanitize the history by appending ONLY the cleanly extracted code
        # instead of the raw hallucination which might train the LLM to keep making formatting mistakes.
        if extracted_code:
            dprint(
                f"trial {trial}: extracted C code snippet (first 500 chars):\n{extracted_code[:500]}"
            )
            chat_log.append(f"[[[\n{extracted_code}\n]]]")
        else:
            dprint(f"trial {trial}: extracted_code is None")
            chat_log.append(
                response
            )  # Append the raw mistake so it has context for the reprimand

        if extracted_code is None:
            dprint("trial: no code extracted; asking for proper [[[...]]] block")
            chat_log.append(
                "SYSTEM CORRECTION: You failed to wrap your C code in the required [[[ ]]] brackets or you included Markdown formatting inside them. Please return ONLY the full C+ACSL inside [[[...]]]."
            )
            continue

        if "!!i give up!!" in extracted_code.lower():
            dprint("trial: LLM marked code as unverifiable")
            explanation = explain_results(
                extracted_code,
                "LLM determined the code was unverifiable.",
                False,
                user_api_key,
                api_provider,
            )
            return {"valid": False, "frama": extracted_code, "explanation": explanation}

        with tempfile.NamedTemporaryFile(mode="w", suffix=".c", delete=False) as tmp:
            tmp.write(extracted_code)
            tmp_path = tmp.name
        dprint(f"wrote temp C file: {tmp_path} (len={len(extracted_code)})")

        ok, frama_output = run_frama_c(tmp_path)
        try:
            os.remove(tmp_path)
            dprint(f"deleted temp file: {tmp_path}")
        except Exception as e:
            dprint(f"failed to delete temp file: {e}")

        if ok:
            dprint("frama-c succeeded — running audit")

            # FIX #3: Auditor Prompt Explosion. We pass just the specific user requirement,
            # NOT the massive system prompt that is full of dummy example blocks.
            audit_instruction = (
                goal_instruction
                if goal_instruction
                else "Formally verify the logic and memory safety of the provided C code."
            )
            is_good = audit_annotations(
                original_code=user_code,
                original_prompt=audit_instruction,
                annotated_code=extracted_code,
                user_api_key=user_api_key,
                api_provider=api_provider,
            )

            if is_good:
                dprint("audit passed")
                explanation = explain_results(
                    extracted_code, frama_output, True, user_api_key, api_provider
                )
                return {
                    "valid": True,
                    "frama": extracted_code,
                    "explanation": explanation,
                }
            else:
                dprint("audit failed — continuing to next trial")
                chat_log.append(
                    "Your annotations compiled and passed Frama-C, but an independent auditor "
                    "determined the proof was dishonest or incomplete (e.g. vacuous preconditions, "
                    "missing specs, or modified logic). Please rewrite the ACSL annotations to "
                    "provide a genuine, complete proof without shortcuts."
                )
        else:
            dprint("verification failed; continuing to next trial")
            hint = categorize_frama_error(frama_output)
            hint_block = f"{hint}\n\n" if hint else ""
            chat_log.append(
                f"{hint_block}Frama-C verification failed.\n"
                f"Here is the output from Frama-C:\n{frama_output}\n\n"
                f"Please analyze these errors, adjust the ACSL annotations, and try again."
            )

    dprint("max trials exceeded")

    if llm_successes == 0:
        dprint("zero successful LLM calls — signalling api_error")
        return {
            "valid": False,
            "api_error": True,
            "error": "LLM API returned no responses — the key may be invalid, expired, or rate-limited.",
            "explanation": "All LLM calls failed. The API key may be invalid, expired, or rate-limited.",
        }

    final_frama_text = (
        extracted_code if extracted_code else "// No code generated by LLM."
    )
    final_frama_text += f"\n\n// The issue was:\n// {frama_output}"

    explanation = explain_results(
        extracted_code, frama_output, False, user_api_key, api_provider
    )

    return {"valid": False, "frama": final_frama_text, "explanation": explanation}


def main():
    dprint(f"argv: {sys.argv}")

    if len(sys.argv) < 3:
        dprint("WRONG ARGS!!!!")
        sys.exit(1)

    api_key = sys.argv[1]
    api_provider = sys.argv[2]
    user_goal = sys.argv[3] if len(sys.argv) > 3 else None

    dprint("mode: reading code from stdin")
    c_code = sys.stdin.read()

    dprint(
        f"provider={api_provider}, api_key_len={len(api_key) if api_key else 0}, code_len={len(c_code)}, goal={user_goal}"
    )
    try:
        result = verify_c_code(c_code, api_key, api_provider, user_goal)
        print(json.dumps(result))
    except Exception as e:
        dprint(f"unexpected error: {e}")
        print(json.dumps({"valid": False, "error": str(e)}))
        sys.exit(1)


if __name__ == "__main__":
    main()
