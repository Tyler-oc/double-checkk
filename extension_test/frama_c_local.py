import sys
import os
import re
import subprocess
import json
import tempfile
import time
from anthropic import Anthropic
from openai import OpenAI
import google.generativeai as genai  # <--- New Import


# ==========================================
# CONFIGURATION - CHANGE THESE
# ==========================================
API_KEY = "ss"
PROVIDER = "google"  # Change to "google", "openai", or "anthropic


CODE_TO_VERIFY = """
int
fac(int n)
{
 return n == 0 ? 1 : n*fac(n - 1);
}


int
main()
{
 return fac(5);
}
"""


USER_GOAL = ""
# ==========================================


def dprint(msg: str):
   sys.stderr.write(f"[DEBUG] {msg}\n")
   sys.stderr.flush()


def extract_code_from_response(response: str):
   if response is None:
       return None
   m = re.search(r"\[\[\[(.*?)\]\]\]", response, re.DOTALL)
   if m:
       return m.group(1).strip()
   return None


def call_llm(chat_log, user_api_key, api_provider: str):
   if not user_api_key or user_api_key == "your-api-key-here":
       dprint("Error: API Key is missing or not set.")
       return None


   try:
       # --- GOOGLE GEMINI IMPLEMENTATION ---
       if api_provider == "google":
           genai.configure(api_key=user_api_key)
           model = genai.GenerativeModel('gemini-3.1-flash-lite-preview')
          
           # Gemini uses a specific history format
           history = []
           for i in range(0, len(chat_log) - 1, 2):
               history.append({"role": "user", "parts": [chat_log[i]]})
               if i + 1 < len(chat_log):
                   history.append({"role": "model", "parts": [chat_log[i+1]]})
          
           # The last message in chat_log is the current prompt
           chat = model.start_chat(history=history)
           response = chat.send_message(chat_log[-1])
           return response.text


       # --- EXISTING PROVIDERS ---
       messages = []
       for i, content in enumerate(chat_log):
           role = "user" if i % 2 == 0 else "assistant"
           messages.append({"role": role, "content": content})


       if api_provider == "anthropic":
           client = Anthropic(api_key=user_api_key)
           resp = client.messages.create(
               model="claude-3-5-sonnet-20240620",
               max_tokens=4000,
               messages=messages,
           )
           return resp.content[0].text


       elif api_provider == "openai":
           client = OpenAI(api_key=user_api_key)
           resp = client.chat.completions.create(
               model="gpt-4o",
               messages=messages,
               max_tokens=4000,
           )
           return resp.choices[0].message.content
          
   except Exception as e:
       dprint(f"LLM call failed: {e}")
       return None


def run_frama_c(c_path: str, timeout_sec=60):
   # Standard WP setup using Z3
   args = ["-wp", "-wp-status-all", "-wp-rte", "-wp-prover", "z3"]
   cmd = ["frama-c", "-quiet"] + args + [c_path]
   dprint(f"Running: {' '.join(cmd)}")
  
   try:
       result = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec)
       full_output = (result.stdout or "") + "\n" + (result.stderr or "")
       # WP is successful if all goals are proved (no "Unknown" or "Timeout")
       # For simplicity, we check if return code is 0
       return result.returncode == 0, full_output
   except Exception as e:
       return False, str(e)


def verify_c_code(user_code: str, user_api_key: str, api_provider: str, user_goal: str = None):
   prompt_base = """
You are an expert in Frama-C/ACSL.
Output the full code enclosed by 3 brackets [[[ ... ]]].
It is vital that the generated code compiles to a valid C program.
"""
   goal_instr = f"\nGoal: {user_goal}\n" if user_goal else ""
   prompt = prompt_base + goal_instr + f"\nCode to verify:\n[[[\n{user_code}\n]]]"


   chat_log = [prompt]
   max_trials = 3 # Reduced trials for local testing speed


   for trial in range(1, max_trials + 1):
       dprint(f"Trial {trial}/{max_trials}...")
       response = call_llm(chat_log, user_api_key, api_provider)
       if not response: continue


       chat_log.append(response)
       extracted_code = extract_code_from_response(response)
      
       if not extracted_code:
           chat_log.append("Please provide the code inside [[[ ]]] brackets.")
           continue


       with tempfile.NamedTemporaryFile(mode="w", suffix=".c", delete=False) as tmp:
           tmp.write(extracted_code)
           tmp_path = tmp.name


       ok, output = run_frama_c(tmp_path)
       os.remove(tmp_path)


       if ok:
           return {"valid": True, "frama_code": extracted_code, "output": output}
       else:
           dprint("Verification failed, retrying...")
           chat_log.append(f"Frama-C failed:\n{output}\nPlease fix the ACSL.")


   return {"valid": False, "error": "Max trials reached without proof."}


if __name__ == "__main__":
   dprint("Starting local verification...")
   res = verify_c_code(CODE_TO_VERIFY, API_KEY, PROVIDER, USER_GOAL)
  
   print("\n" + "="*30)
   if res.get("valid"):
       print("SUCCESS: Code Verified")
       print(res["frama_code"])
   else:
       print("FAILED")
       print(res.get("error") or res.get("output"))
   print("="*30)

