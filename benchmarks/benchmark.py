import os
import csv
import time
import requests
from datetime import datetime

# --- CONFIGURATION ---
BENCHMARK_DIR = os.path.join(os.path.dirname(__file__), "sv_comp")
RESULTS_FILE = os.path.join(
    os.path.dirname(__file__), f"results_{datetime.now().strftime('%Y%m%d_%H%M')}.csv"
)

# Or use "http://127.0.0.1:8080/verify" if running the Docker container locally
API_URL = "https://double-checkk-api-285186236951.us-central1.run.app/verify"


def run_benchmark():
    tasks = []
    for root, dirs, files in os.walk(BENCHMARK_DIR):
        for file in files:
            if file.endswith(".c"):
                tasks.append(os.path.join(root, file))

    print(f"🚀 Found {len(tasks)} benchmark files. Sending to Cloud Run API...")

    with open(RESULTS_FILE, mode="w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["Category", "Filename", "Status", "Duration", "Error"])

        for i, file_path in enumerate(tasks):
            category = os.path.basename(os.path.dirname(file_path))
            filename = os.path.basename(file_path)

            with open(file_path, "r", encoding="utf-8") as cf:
                code = cf.read()

            print(
                f"[{i+1}/{len(tasks)}] Verifying {category}/{filename}...",
                end="",
                flush=True,
            )

            success = False
            start_time = time.time()

            while not success:
                try:
                    # Send the request to your Cloud Run server
                    # We pass 'FALLBACK' to trigger the round-robin pool you built in main.py
                    headers = {"Authorization": "Bearer FALLBACK"}
                    payload = {"code": code, "provider": "gemini"}

                    # Timeout set to 300s (5 mins) to match your Cloud Run max timeout
                    response = requests.post(
                        API_URL, json=payload, headers=headers, timeout=300
                    )

                    # Handle Cloud Run telling us the fallback pool is exhausted (Rate Limits)
                    if response.status_code == 503 or response.status_code == 429:
                        print(
                            " [SERVER RATE LIMITED] - Pool exhausted. Waiting 60s...",
                            end="",
                            flush=True,
                        )
                        time.sleep(60)
                        continue  # Retry the same file

                    # Raise an error if it's a 500 server crash
                    response.raise_for_status()

                    # Parse successful API response
                    res_data = response.json()
                    duration = round(time.time() - start_time, 2)
                    status = "PASSED" if res_data.get("valid") else "FAILED"
                    error_msg = res_data.get("explanation", "")

                    writer.writerow([category, filename, status, duration, error_msg])
                    f.flush()

                    print(f" {status} ({duration}s)")
                    success = True

                    # Small breath to avoid hammering your own server
                    time.sleep(2)

                except requests.exceptions.RequestException as e:
                    # This catches network drops or 500 errors
                    print(f" [CRASH/NETWORK ERROR] {str(e)}")
                    writer.writerow([category, filename, "CRASH", 0, str(e)])
                    success = True  # Skip to next file to prevent infinite loops

    print(f"\n✅ Benchmark Complete! Results saved to {RESULTS_FILE}")


if __name__ == "__main__":
    run_benchmark()
