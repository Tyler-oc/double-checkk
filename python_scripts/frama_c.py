import sys
import os
from anthropic import Anthropic
import openai

# from google import genai
import re
import subprocess
import json
import tempfile
import time


def dprint(msg: str):
    sys.stderr.write(f"[DEBUG] {msg}\n")
    sys.stderr.flush()


def extract_code_from_response(response: str):
    dprint(
        f"extract_code_from_response: response_len={response if response is not None else 'None'}"
    )
    if response is None:
        return None
    m = re.search(r"\[\[\[(.*?)\]\]\]", response, re.DOTALL)
    if m:
        code = m.group(1).strip()
        dprint(f"extracted ACSL/C block, len={code}")
        return code
    dprint("no [[[...]]] block found in response")
    return None


def call_llm(chat_log, user_api_key, api_provider: str):
    dprint(
        f"call_llm: provider={api_provider}, msgs={chat_log}, api_key_len={len(user_api_key) if user_api_key else 0}"
    )
    if not user_api_key:
        dprint("missing api key")
        return None

    try:
        if api_provider == "anthropic":
            client = Anthropic(api_key=user_api_key)
            # Build alternating user/assistant structure
            messages = []
            for i, content in enumerate(chat_log):
                role = "user" if i % 2 == 0 else "assistant"
                messages.append({"role": role, "content": content})
            dprint(f"anthropic: sending {len(messages)} messages")
            resp = client.messages.create(
                model="claude-3-haiku-20240307",
                max_tokens=400,
                messages=messages,
            )
            text = resp.content[0].text if resp and resp.content else ""
            dprint(f"anthropic: got response_len={len(text)}")
            return text

        elif api_provider == "openai":
            openai.api_key = user_api_key
            dprint("openai: sending prompt as single string")
            formatted = openai.Completion.create(
                model="gpt-5-2025-08-07",  # placeholder
                prompt="\n\n".join(map(str, chat_log)),
                max_tokens=10000,
                n=1,
            )
            text = formatted["choices"][0]["text"].strip()
            dprint(f"openai: got response_len={len(text)}")
            return text

        # elif api_provider == "google":
        #     genai.configure(api_key=user_api_key)
        #     model = genai.GenerativeModel("gemini-2.5-pro")
        #     dprint("google: sending prompt as single string")
        #     out = model.generate_content("\n\n".join(map(str, chat_log)))
        #     text = getattr(out, "text", "") or ""
        #     dprint(f"google: got response_len={len(text)}")
        #     return text

        else:
            dprint(f"unknown provider: {api_provider}")
            return None
    except Exception as e:
        dprint(f"LLM call failed: {e}")
        return None


def run_frama_c(c_path: str, extra_args=None, timeout_sec=60):
    args = extra_args or ["-wp", "-wp-status-all", "-wp-rte", "-wp-prover", "z3"]
    cmd = ["frama-c", "-quiet"] + args + [c_path]
    dprint(f"running: {' '.join(cmd)}")
    t0 = time.time()
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout_sec
        )
        dur = time.time() - t0
        dprint(
            f"frama-c: rc={result.returncode}, elapsed={dur:.2f}s, stdout_len={len(result.stdout)}, stderr_len={len(result.stderr)}"
        )
        full_output = (result.stdout or "") + "\n" + (result.stderr or "")
        if result.stdout:
            dprint("frama-c stdout (first 500 chars):\n" + result.stdout[:500])
        if result.stderr:
            dprint("frama-c stderr (first 500 chars):\n" + result.stderr[:500])
        return result.returncode == 0, full_output
    except subprocess.TimeoutExpired as e:
        dprint(f"frama-c timeout after {timeout_sec}s")
        return False, "Frama-C execution timed out."
    except FileNotFoundError:
        dprint("frama-c not found on PATH")
        return False, "Frama-C executable not found."
    except Exception as e:
        dprint(f"frama-c failed: {e}")
        return False, str(e)


def verify_c_code(user_code: str, user_api_key: str, api_provider: str):
    dprint(
        f"verify_c_code: code_len={len(user_code) if user_code else 0}, provider={api_provider}"
    )
    if not user_code:
        return {"valid": False, "error": "empty code"}

    prompt = (
        """
Example 1 ACSL Professional Coding Agent Output: [[[/*@ requires length > 0; requires \valid_read(arr + (0..length-1)); assigns \nothing; ensures \exists integer k; 0 <= k < length && \result == arr[k]; ensures \forall integer i; 0 <= i < length ==> \result >= arr[i]; */ int find_max(int arr[], int length) { int max = arr[0]; /*@ loop invariant 0 <= i <= length; loop invariant \forall integer j; 0 <= j < i ==> max >= arr[j]; loop invariant \exists integer k; 0 <= k < length && max == arr[k]; loop assigns i, max; loop variant length - i; */ for(int i = 1; i < length; i++) { if (arr[i] > max) { max = arr[i]; } } return max; } /*@ assigns \nothing; */ int main() { int arr[] = {1, 2, 4, 2, 8, 3}; int length = 6; int result = find_max(arr, length); return 0; } ]]]

Example 2 ACSL Professional Coding Agent Output: [[[/*@ logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n - 1); */ /*@ requires n >= 0; requires n <= 12; assigns \nothing; ensures \result == factorial(n); */ int compute_factorial(int n) { int i, f; f = 1; /*@ loop invariant 1 <= i <= n + 1; loop invariant f == factorial(i - 1); loop invariant f >= 1; loop invariant 1 <= i <= 13; loop invariant i == 1 ==> f == 1; loop invariant i == 2 ==> f == 1; loop invariant i == 3 ==> f == 2; loop invariant i == 4 ==> f == 6; loop invariant i == 5 ==> f == 24; loop invariant i == 6 ==> f == 120; loop invariant i == 7 ==> f == 720; loop invariant i == 8 ==> f == 5040; loop invariant i == 9 ==> f == 40320; loop invariant i == 10 ==> f == 362880; loop invariant i == 11 ==> f == 3628800; loop invariant i == 12 ==> f == 39916800; loop invariant i == 13 ==> f == 479001600; loop assigns i, f; loop variant n - i + 1; */ for (i = 1; i <= n; i++) f = f * i; return f; } /*@ assigns \nothing; */ int main() { int n = 5, i, f; f = 1; /*@ loop invariant 1 <= i <= n + 1; loop invariant f == factorial(i - 1); loop invariant f >= 1; loop invariant i == 1 ==> f == 1; loop invariant i == 2 ==> f == 1; loop invariant i == 3 ==> f == 2; loop invariant i == 4 ==> f == 6; loop invariant i == 5 ==> f == 24; loop invariant i == 6 ==> f == 120; loop assigns i, f; loop variant n - i + 1; */ for (i = 1; i <= n; i++) f = f * i; return f; } ]]]

Example 3 ACSL Professional Coding Agent Output: [[[ /*@ logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n - 1); */ /*@ assigns \nothing; ensures \result == factorial(5); */ int main() { int s, r, n = 5, u, v; /* keep an explicit runtime/verification check for n bounds */ /*@ assert 0 <= n <= 12; */ /* Outer loop: - r runs from 1 up to n-1, - u == factorial(r) at loop head */ /*@ loop invariant 1 <= r <= n; loop invariant u == factorial(r); loop assigns r, s, u, v; loop variant n - r; */ for (u = r = 1; r < n; r++) { v = u; /* Inner loop rewritten as a simple counting loop: u += v executed r times */ /*@ loop invariant 0 <= s <= r; loop invariant u == v * (s + 1); loop assigns s, u; loop variant r - s; */ for (s = 0; s < r; ++s) { u += v; } /* now u == v * (r + 1) == factorial(r+1) */ /*@ assert u == factorial(r + 1); */ } return u; } ]]] 

Example 4 ACSL Professional Coding Agent Output: [[[UNVERIFIABLE: recursive calls were made unguarded. Passing j - m + 1 or n - i + 1 could become 0 or negative.]]]

You are an expert in Frama-C/ACSL. Please verify my code (attached below)
 using ACSL specifications. Refer to the above examples as a guide. 
 You may think before outputting your code but when you are done, 
 output the full code enclosed by 3 brackets (it will be extracted 
 and the proof will be automatically run). If the code is unverifiable 
 (ie. because the function has an error or hole) simply write unverifiable
  followed by a small explanation within the brackets. I am sending you the
   code to be verified, it is most important that you do not modify any part
    of the code. If the code is unverifiable (ie. bad code/ bad specification) simply say '!!i give up!!'. 
    You must only write ACSL on top of the already implemented code, 
    and wrap the code in any function / include statements necessary to create a valid c program.
It is vital that the generated code compiles to a valid C program.
     Now, here is the code to be verified: [[[
"""
        + user_code
        + """]]]
"""
    )

    chat_log = [prompt]
    max_trials = 6

    for trial in range(1, max_trials + 1):
        dprint(f"trial {trial}/{max_trials}: calling LLM")
        response = call_llm(chat_log, user_api_key, api_provider)
        if response is None:
            dprint("trial: LLM returned None")
            chat_log.append("LLM error or no response")
            continue

        chat_log.append(response)
        extracted_code = extract_code_from_response(response)
        if extracted_code is None:
            dprint("trial: no code extracted; asking for proper [[[...]]] block")
            chat_log.append("Please return ONLY full C+ACSL inside [[[...]]].")
            continue

        if "!!i give up!!" in extracted_code.lower():
            dprint("trial: LLM marked code as unverifiable")
            return {"valid": False, "frama": "trial: LLM marked code as unverifiable"}

        # Write to a temp file and run Frama-C
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
            dprint("verification succeeded")
            return {"valid": True, "frama": extracted_code}
        else:
            dprint("verification failed; continuing to next trial")
            chat_log.append(
                f"Frama-C verification failed.\n"
                f"Here is the output from Frama-C:\n{frama_output}\n\n"
                f"Please analyze these errors, adjust the ACSL annotations, and try again."
            )

    dprint("max trials exceeded")
    return {
        "valid": False,
        "frama": extracted_code + "\n The issue was: " + frama_output,
    }


def main():
    dprint(f"argv: {sys.argv}")
    # Support two modes:
    # 1) argv: script code api_key provider
    # 2) argv: script api_key provider, code on stdin (recommended for long inputs)
    if len(sys.argv) != 3:
        dprint("WRONG!!!!")
        sys.exit(1)
    api_key = sys.argv[1]
    api_provider = sys.argv[2]
    dprint("mode: reading code from stdin")
    c_code = sys.stdin.read()

    dprint(
        f"provider={api_provider}, api_key_len={len(api_key) if api_key else 0}, code_len={len(c_code)}"
    )
    try:
        result = verify_c_code(c_code, api_key, api_provider)
        print(json.dumps(result))
    except Exception as e:
        dprint(f"unexpected error: {e}")
        print(json.dumps({"valid": False, "error": str(e)}))
        sys.exit(1)


if __name__ == "__main__":
    main()
