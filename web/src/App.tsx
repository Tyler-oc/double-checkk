import { useState } from "react";
import Editor from "@monaco-editor/react";

const DEFAULT_CODE = `#include <stdio.h>

int sum_to_n(int n) {
  int result = 0;
  
  for (int i = 1; i <= n; i++) {
    result += i;
  }
  return result;
}

int main() {
  printf("Sum 1..10 = %d\\n", sum_to_n(10));
  return 0;
}`;

const BACKEND_URL =
  "https://double-checkk-api-285186236951.us-central1.run.app/verify";

type VerifyResult = {
  valid: boolean;
  frama?: string;
  error?: string;
  status?: string; // keeping your old status just in case
  output?: string; // keeping your old output just in case
};

export default function App() {
  const [code, setCode] = useState(DEFAULT_CODE);
  const [userGoal, setUserGoal] = useState("");
  const [result, setResult] = useState<VerifyResult | null>(null);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  async function handleVerify() {
    setLoading(true);
    setError(null);
    setResult(null);
    try {
      const response = await fetch(BACKEND_URL, {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          Authorization: "Bearer FALLBACK",
        },
        body: JSON.stringify({
          code: code,
          provider: "openai", // Hardcoded for the web demo, or you can add a dropdown later!
          user_goal: userGoal.trim() !== "" ? userGoal : null,
        }),
      });

      const data = await response.json();

      if (!response.ok) {
        throw new Error(data.detail || `Server returned ${response.status}`);
      }

      setResult(data);
    } catch (err) {
      setError(err instanceof Error ? err.message : "Request failed");
    } finally {
      setLoading(false);
    }
  }

  return (
    <div className="min-h-screen bg-gray-950 text-gray-100 font-sans">
      {/* Header */}
      <header className="border-b border-gray-800 px-6 py-5">
        <div className="max-w-7xl mx-auto flex items-center gap-4">
          <div className="flex items-center gap-2">
            <span className="text-green-400 text-2xl font-bold font-mono">
              &#10003;
            </span>
            <h1 className="text-xl font-bold tracking-tight text-white">
              Double Check
            </h1>
          </div>
          <span className="text-gray-500 text-sm">|</span>
          <p className="text-gray-400 text-sm hidden sm:block">
            Formally verifies C code using AI and Frama-C
          </p>
        </div>
      </header>

      {/* Hero */}
      <section className="max-w-7xl mx-auto px-6 pt-12 pb-8 text-center">
        <div className="inline-flex items-center gap-2 bg-green-900/30 border border-green-700/50 rounded-full px-4 py-1.5 text-green-400 text-xs font-medium mb-6">
          <span className="w-1.5 h-1.5 rounded-full bg-green-400 animate-pulse" />
          Powered by Frama-C + AI
        </div>
        <h2 className="text-4xl md:text-5xl font-bold text-white mb-4 tracking-tight">
          Prove your C code is correct.
        </h2>
        <p className="text-gray-400 text-lg max-w-2xl mx-auto">
          Paste any C function, describe what it should do, and let Double Check
          formally verify it using Frama-C&apos;s WP plugin — no manual proof
          required.
        </p>
      </section>

      {/* Two-column editor + output */}
      <main className="max-w-7xl mx-auto px-6 pb-16">
        <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
          {/* Left: Editor & Controls */}
          <div className="flex flex-col gap-4">
            <div className="rounded-xl overflow-hidden border border-gray-800 shadow-2xl">
              <div className="flex items-center gap-2 bg-gray-900 px-4 py-2.5 border-b border-gray-800">
                <span className="w-3 h-3 rounded-full bg-red-500/80" />
                <span className="w-3 h-3 rounded-full bg-yellow-500/80" />
                <span className="w-3 h-3 rounded-full bg-green-500/80" />
                <span className="ml-2 text-gray-500 text-xs font-mono">
                  main.c
                </span>
              </div>
              <Editor
                height="400px"
                defaultLanguage="c"
                theme="vs-dark"
                value={code}
                onChange={(val) => setCode(val ?? "")}
                options={{
                  fontSize: 13,
                  minimap: { enabled: false },
                  scrollBeyondLastLine: false,
                  lineNumbers: "on",
                  tabSize: 2,
                  wordWrap: "on",
                  padding: { top: 12, bottom: 12 },
                }}
              />
            </div>

            {/* NEW: User Goal Input */}
            <div className="flex flex-col gap-1.5">
              <label
                htmlFor="userGoal"
                className="text-sm font-medium text-gray-400 ml-1"
              >
                What should this code do?{" "}
                <span className="text-gray-600">(Optional)</span>
              </label>
              <input
                id="userGoal"
                type="text"
                value={userGoal}
                onChange={(e) => setUserGoal(e.target.value)}
                placeholder="e.g. Ensure the result is strictly positive"
                className="w-full bg-gray-900 border border-gray-800 rounded-xl px-4 py-3 text-sm text-gray-200 placeholder-gray-600 focus:outline-none focus:ring-1 focus:ring-green-500/50 transition-all shadow-inner"
              />
            </div>

            <button
              onClick={handleVerify}
              disabled={loading}
              className="w-full bg-green-600 hover:bg-green-500 disabled:bg-gray-700 disabled:text-gray-500 text-white font-bold py-3.5 px-6 rounded-xl transition-colors duration-150 flex items-center justify-center gap-2 text-sm tracking-wide mt-1"
            >
              {loading ? (
                <>
                  <span className="w-4 h-4 border-2 border-white/30 border-t-white rounded-full animate-spin" />
                  Verifying...
                </>
              ) : (
                <>
                  <span>&#10003;</span>
                  Formally Verify Code
                </>
              )}
            </button>
          </div>

          {/* Right: Output terminal */}
          <div className="flex flex-col">
            <div className="rounded-xl overflow-hidden border border-gray-800 shadow-2xl flex-1 flex flex-col h-full min-h-[500px]">
              <div className="flex items-center gap-2 bg-gray-900 px-4 py-2.5 border-b border-gray-800">
                <span className="w-3 h-3 rounded-full bg-red-500/80" />
                <span className="w-3 h-3 rounded-full bg-yellow-500/80" />
                <span className="w-3 h-3 rounded-full bg-green-500/80" />
                <span className="ml-2 text-gray-500 text-xs font-mono">
                  frama-c output
                </span>
                {result && (
                  <span
                    className={`ml-auto text-xs font-medium px-2 py-0.5 rounded-full ${
                      result.valid || result.status === "success"
                        ? "bg-green-900/60 text-green-400"
                        : "bg-red-900/60 text-red-400"
                    }`}
                  >
                    {result.valid || result.status === "success"
                      ? "verified"
                      : "failed"}
                  </span>
                )}
              </div>

              <div className="bg-gray-950 flex-1 p-4 font-mono text-sm overflow-auto">
                {!result && !error && !loading && (
                  <div className="flex flex-col items-center justify-center h-full gap-3 text-gray-600 mt-20">
                    <svg
                      className="w-10 h-10"
                      fill="none"
                      stroke="currentColor"
                      viewBox="0 0 24 24"
                    >
                      <path
                        strokeLinecap="round"
                        strokeLinejoin="round"
                        strokeWidth={1.5}
                        d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z"
                      />
                    </svg>
                    <p className="text-sm">
                      Click &quot;Formally Verify Code&quot; to run Frama-C
                    </p>
                  </div>
                )}

                {loading && (
                  <div className="flex flex-col items-center justify-center h-full gap-3 text-gray-500 mt-20">
                    <span className="w-8 h-8 border-2 border-gray-600 border-t-green-400 rounded-full animate-spin" />
                    <p className="text-sm">Running Frama-C WP analysis...</p>
                  </div>
                )}

                {error && (
                  <div className="text-red-400 mt-4">
                    <span className="text-red-600 font-bold">Error: </span>
                    {error}
                  </div>
                )}

                {result && (
                  <div className="space-y-2">
                    <div
                      className={
                        result.valid || result.status === "success"
                          ? "text-green-400"
                          : "text-red-400"
                      }
                    >
                      <span className="text-gray-500">$ </span>
                      frama-c -wp main.c
                    </div>

                    {/* Display the newly generated Frama-C code/output */}
                    <pre className="text-gray-300 whitespace-pre-wrap leading-relaxed mt-2">
                      {result.frama ??
                        result.output ??
                        result.error ??
                        JSON.stringify(result, null, 2)}
                    </pre>

                    <div
                      className={`mt-4 font-bold ${
                        result.valid || result.status === "success"
                          ? "text-green-400"
                          : "text-red-400"
                      }`}
                    >
                      {result.valid || result.status === "success"
                        ? "All goals proved."
                        : "Verification failed."}
                    </div>
                  </div>
                )}
              </div>
            </div>
          </div>
        </div>
      </main>
    </div>
  );
}
