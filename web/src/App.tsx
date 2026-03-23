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
  status?: string;
  output?: string;
  explanation?: string; // NEW: The AI translation of the Frama-C logs
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
          provider: "openai",
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
    <div className="min-h-screen bg-[#0d1117] text-zinc-300 font-sans selection:bg-blue-500/30">
      {/* Navbar - IDE Style */}
      <header className="border-b border-zinc-800 bg-[#010409] px-6 py-3 flex items-center justify-between">
        <div className="flex items-center gap-3">
          <div className="w-4 h-4 bg-blue-500 rounded-sm"></div>
          <h1 className="text-lg font-semibold tracking-wide text-zinc-100 font-mono">
            Double_Check
          </h1>
          <span className="text-zinc-600 px-2">|</span>
          <span className="text-xs font-mono text-zinc-400 hidden sm:block">
            v1.0.0-beta [Formal Verification Engine]
          </span>
        </div>
      </header>

      {/* Main Workspace */}
      <main className="max-w-[1600px] mx-auto p-4 md:p-6 lg:p-8">
        {/* CLI-style Intro */}
        <div className="mb-6 font-mono text-sm text-zinc-400">
          <p className="text-zinc-300 mb-1">$ ./double-check --help</p>
          <p className="pl-4 border-l-2 border-zinc-800">
            Automated Frama-C WP prover. Write C code, declare intent, and
            verify mathematically.
          </p>
        </div>

        {/* IDE Split View */}
        <div className="grid grid-cols-1 lg:grid-cols-2 gap-4 lg:gap-6">
          {/* LEFT PANEL: Editor & Config */}
          <div className="flex flex-col gap-4">
            {/* Editor Window */}
            <div className="rounded border border-zinc-800 bg-[#0d1117] overflow-hidden shadow-lg flex flex-col">
              {/* File Tab */}
              <div className="flex text-xs font-mono text-zinc-500 bg-[#010409] border-b border-zinc-800">
                <div className="px-4 py-2 bg-[#0d1117] border-r border-zinc-800 text-zinc-200 border-t-2 border-t-blue-500">
                  main.c
                </div>
              </div>
              <Editor
                height="450px"
                defaultLanguage="c"
                theme="vs-dark"
                value={code}
                onChange={(val) => setCode(val ?? "")}
                options={{
                  fontSize: 13,
                  fontFamily: "'JetBrains Mono', 'Fira Code', monospace",
                  minimap: { enabled: false },
                  scrollBeyondLastLine: false,
                  lineNumbers: "on",
                  tabSize: 2,
                  padding: { top: 16, bottom: 16 },
                }}
              />
            </div>

            {/* Config & Execution Panel */}
            <div className="rounded border border-zinc-800 bg-[#010409] p-4 flex flex-col gap-4 shadow-lg">
              <div className="flex flex-col gap-2">
                <label
                  htmlFor="userGoal"
                  className="text-xs font-mono text-zinc-400 uppercase tracking-wider"
                >
                  Verification Goal (Optional)
                </label>
                <input
                  id="userGoal"
                  type="text"
                  value={userGoal}
                  onChange={(e) => setUserGoal(e.target.value)}
                  placeholder="e.g. Ensure the result is strictly positive"
                  className="w-full bg-[#0d1117] border border-zinc-800 rounded px-3 py-2 text-sm font-mono text-zinc-200 placeholder-zinc-700 focus:outline-none focus:border-blue-500 focus:ring-1 focus:ring-blue-500 transition-colors"
                />
              </div>

              <button
                onClick={handleVerify}
                disabled={loading}
                className="w-full bg-blue-600 hover:bg-blue-500 disabled:bg-zinc-800 disabled:text-zinc-500 text-white font-mono text-sm py-2.5 px-4 rounded transition-colors flex items-center justify-center gap-2 uppercase tracking-wide"
              >
                {loading ? (
                  <>
                    <span className="w-3.5 h-3.5 border-2 border-white/30 border-t-white rounded-full animate-spin" />
                    Running Prover...
                  </>
                ) : (
                  <>
                    <span>►</span> Execute Verification
                  </>
                )}
              </button>
            </div>
          </div>

          {/* RIGHT PANEL: Output Console */}
          <div className="flex flex-col h-full min-h-[500px]">
            <div className="rounded border border-zinc-800 bg-black flex-1 flex flex-col shadow-lg overflow-hidden">
              {/* Output Tab Bar */}
              <div className="flex items-center justify-between text-xs font-mono text-zinc-500 bg-[#010409] border-b border-zinc-800 pr-4">
                <div className="px-4 py-2 bg-black border-r border-zinc-800 text-zinc-200">
                  TERMINAL
                </div>
                {result && (
                  <span
                    className={`px-2 py-0.5 rounded-sm uppercase tracking-wider text-[10px] font-bold ${
                      result.valid || result.status === "success"
                        ? "bg-green-500/10 text-green-400 border border-green-500/20"
                        : "bg-red-500/10 text-red-400 border border-red-500/20"
                    }`}
                  >
                    {result.valid || result.status === "success"
                      ? "PASS"
                      : "FAIL"}
                  </span>
                )}
              </div>

              {/* Scrollable Output Area */}
              <div className="p-4 overflow-auto flex-1 font-mono text-[13px] leading-relaxed">
                {/* Idle State */}
                {!result && !error && !loading && (
                  <div className="text-zinc-600 h-full flex flex-col items-center justify-center mt-20">
                    <p className="mb-2">&gt; Engine ready.</p>
                    <p>&gt; Waiting for input...</p>
                  </div>
                )}

                {/* Loading State */}
                {loading && (
                  <div className="text-blue-400 flex items-center gap-3 mt-4">
                    <span className="w-2 h-4 bg-blue-400 animate-pulse" />
                    <span>Analyzing AST and generating ACSL invariants...</span>
                  </div>
                )}

                {/* Error State */}
                {error && (
                  <div className="text-red-400 mt-4 border-l-2 border-red-500 pl-3">
                    <span className="font-bold">FATAL: </span>
                    {error}
                  </div>
                )}

                {/* Success/Result State */}
                {result && (
                  <div className="space-y-6">
                    {/* NEW: AI Explanation Box */}
                    {result.explanation && (
                      <div className="border-l-2 border-blue-500 bg-blue-950/20 p-4 rounded-r-md">
                        <div className="text-blue-400 font-bold text-xs uppercase tracking-wider mb-2 flex items-center gap-2">
                          <span className="w-1.5 h-1.5 rounded-full bg-blue-400 animate-pulse" />
                          AI Diagnostic Summary
                        </div>
                        <p className="text-blue-100 font-sans text-sm leading-relaxed">
                          {result.explanation}
                        </p>
                      </div>
                    )}

                    {/* Raw Frama-C Log */}
                    <div>
                      <div className="text-zinc-500 mb-2">
                        $ frama-c -wp main.c
                      </div>
                      <pre className="text-zinc-300 whitespace-pre-wrap">
                        {result.frama ??
                          result.output ??
                          result.error ??
                          JSON.stringify(result, null, 2)}
                      </pre>
                    </div>

                    {/* Final Status Line */}
                    <div
                      className={`pt-4 border-t border-zinc-800 ${
                        result.valid || result.status === "success"
                          ? "text-green-400"
                          : "text-red-400"
                      }`}
                    >
                      &gt; Process exited with code{" "}
                      {result.valid || result.status === "success" ? "0" : "1"}.
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
