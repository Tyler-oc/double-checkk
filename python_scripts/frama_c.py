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
    
    prompt = ""
    with open("./prompt.txt", 'r') as f:
        prompt = f.read()
    dprint(f"prompt_len={len(prompt)}")

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
            return {"valid": False}

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
            return {"valid": True}
        else:
            dprint("verification failed; continuing to next trial")
            chat_log.append(
                f"Frama-C verification failed.\n"
                f"Here is the output from Frama-C:\n{frama_output}\n\n"
                f"Please analyze these errors, adjust the ACSL annotations, and try again."
            )

    dprint("max trials exceeded")
    return {"valid": False}


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
