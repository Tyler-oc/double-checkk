import sys
import os
from anthropic import Anthropic
import openai
from google import genai
import re
import subprocess
import json
import subprocess
import tempfile
import os


def extract_code_from_response(response):
    match = re.search(r'\[\[\[(.*?)\]\]\]', response, re.DOTALL)
    if match:
        return match.group(1).strip()
    else:
        return None


def call_llm(chat_log, user_api_key, api_provider):
    if not user_api_key:
        return False
    
    if api_provider == "anthropic":
        client = Anthropic(api_key=user_api_key)
        messages = []
        for i, content in enumerate(chat_log):
            role = "user" if i % 2 == 0 else "assistant"
            messages.append({"role": role, "content": content})
        
        response = client.messages.create(
            model="claude-sonnet-4-5-20250929",
            max_tokens=10000,
            messages=messages
        ).content[0].text

    if api_provider == "openai":
        openai.api_key = user_api_key
        formatted_response = openai.Completion.create(
            model="gpt-5-2025-08-07",
            prompt=chat_log, #TODO
            max_tokens=10000,
            n=1
        )
        response = formatted_response['choices'][0]['text'].strip() 

    if api_provider == "google":
        genai.configure(api_key=user_api_key)
        model = genai.GenerativeModel('gemini-2.5-pro')
        response = model.generate_content(chat_log).text #TODO

    return response


def verify_c_code(user_code, user_api_key, api_provider: str) -> bool:
    if not user_code:
        return False

    prompt = """
        Example 1 ACSL Professional Coding Agent Output: [[[/*@ requires length > 0; requires \valid_read(arr + (0..length-1)); assigns \nothing; ensures \exists integer k; 0 <= k < length && \result == arr[k]; ensures \forall integer i; 0 <= i < length ==> \result >= arr[i]; */ int find_max(int arr[], int length) { int max = arr[0]; /*@ loop invariant 0 <= i <= length; loop invariant \forall integer j; 0 <= j < i ==> max >= arr[j]; loop invariant \exists integer k; 0 <= k < length && max == arr[k]; loop assigns i, max; loop variant length - i; */ for(int i = 1; i < length; i++) { if (arr[i] > max) { max = arr[i]; } } return max; } /*@ assigns \nothing; */ int main() { int arr[] = {1, 2, 4, 2, 8, 3}; int length = 6; int result = find_max(arr, length); return 0; } ]]]

        Example 2 ACSL Professional Coding Agent Output: [[[/*@ logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n - 1); */ /*@ requires n >= 0; requires n <= 12; assigns \nothing; ensures \result == factorial(n); */ int compute_factorial(int n) { int i, f; f = 1; /*@ loop invariant 1 <= i <= n + 1; loop invariant f == factorial(i - 1); loop invariant f >= 1; loop invariant 1 <= i <= 13; loop invariant i == 1 ==> f == 1; loop invariant i == 2 ==> f == 1; loop invariant i == 3 ==> f == 2; loop invariant i == 4 ==> f == 6; loop invariant i == 5 ==> f == 24; loop invariant i == 6 ==> f == 120; loop invariant i == 7 ==> f == 720; loop invariant i == 8 ==> f == 5040; loop invariant i == 9 ==> f == 40320; loop invariant i == 10 ==> f == 362880; loop invariant i == 11 ==> f == 3628800; loop invariant i == 12 ==> f == 39916800; loop invariant i == 13 ==> f == 479001600; loop assigns i, f; loop variant n - i + 1; */ for (i = 1; i <= n; i++) f = f * i; return f; } /*@ assigns \nothing; */ int main() { int n = 5, i, f; f = 1; /*@ loop invariant 1 <= i <= n + 1; loop invariant f == factorial(i - 1); loop invariant f >= 1; loop invariant i == 1 ==> f == 1; loop invariant i == 2 ==> f == 1; loop invariant i == 3 ==> f == 2; loop invariant i == 4 ==> f == 6; loop invariant i == 5 ==> f == 24; loop invariant i == 6 ==> f == 120; loop assigns i, f; loop variant n - i + 1; */ for (i = 1; i <= n; i++) f = f * i; return f; } ]]]

        Example 3 ACSL Professional Coding Agent Output: [[[ /*@ logic integer factorial(integer n) = (n <= 0) ? 1 : n * factorial(n - 1); */ /*@ assigns \nothing; ensures \result == factorial(5); */ int main() { int s, r, n = 5, u, v; /* keep an explicit runtime/verification check for n bounds */ /*@ assert 0 <= n <= 12; */ /* Outer loop: - r runs from 1 up to n-1, - u == factorial(r) at loop head */ /*@ loop invariant 1 <= r <= n; loop invariant u == factorial(r); loop assigns r, s, u, v; loop variant n - r; */ for (u = r = 1; r < n; r++) { v = u; /* Inner loop rewritten as a simple counting loop: u += v executed r times */ /*@ loop invariant 0 <= s <= r; loop invariant u == v * (s + 1); loop assigns s, u; loop variant r - s; */ for (s = 0; s < r; ++s) { u += v; } /* now u == v * (r + 1) == factorial(r+1) */ /*@ assert u == factorial(r + 1); */ } return u; } ]]] 

        Example 4 ACSL Professional Coding Agent Output: [[[UNVERIFIABLE: recursive calls were made unguarded. Passing j - m + 1 or n - i + 1 could become 0 or negative.]]]

        You are an expert in Frama-C/ACSL. Please verify my code (attached below) 
        using ACSL specifications. Refer to the above examples as a guide. You may 
        think before outputting your code but when you are done, output the full code 
        enclosed by 3 brackets (it will be extracted and the proof will be automatically 
        run). If the code is unverifiable (ie. because the function has an error or hole) 
        simply write unverifiable followed by a small explanation within the brackets. I am 
        sending you the code to be verified, it is most important that you do not change any 
        part of the code. You must only write ACSL on top of the already implemented code. 
        Now, here is the code to be verified: [[[
        """ + user_code + """]]] """
    
    num_trials = 6
    chat_log = []
    chat_log.append(prompt)
    for trial in range(num_trials):
        response = call_llm(chat_log, user_api_key, api_provider)
        chat_log.append(response)
        extracted_code = extract_code_from_response(response)
        if "unverifiable" in extracted_code.lower():
            return {"valid": False, "frama": extracted_code}
        else:
            with tempfile.NamedTemporaryFile(
                mode='w',
                suffix='.c',
                delete=False
            ) as tmp_file:
                tmp_file.write(extracted_code)
            tmp_filename = tmp_file.name
            cmd = [
                'frama-c',
                '-wp',
                '-wp-status-all',
                '-wp-rte',
                '-wp-prover', 'z3',
                tmp_filename
            ]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
            if result.returncode == 0:
                return {"valid": True, "frama": extracted_code}
            chat_log.append(result)

    return {"valid": False, "frama": "Max tries exceeded."}



def main():
    if len(sys.argv) != 4:
        print("Make sure code is highlighted and api key is entered")
        sys.exit(1)
    c_code = sys.argv[1]
    api_key = sys.argv[2]
    api_provider = sys.argv[3]
    return verify_c_code(c_code, api_key, api_provider)


if __name__ == "__main__":
    main()
