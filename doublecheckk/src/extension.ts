import * as vscode from 'vscode';
import * as cp from 'child_process'; // or use fetch if backend is HTTP

export function activate(context: vscode.ExtensionContext) {
    let disposable = vscode.commands.registerCommand('doublecheckk.verifySelection', async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor) {
            vscode.window.showErrorMessage("No active editor");
            return;
        }

        const selection = editor.document.getText(editor.selection);
        if (!selection) {
            vscode.window.showErrorMessage("No code selected");
            return;
        }

        vscode.window.showInformationMessage("Sending selection to DoubleCheckk...");

        try {
            // --- OPTION A: if your backend is a local process ---
            // let result = runBackendProcess(selection);

            // --- OPTION B: if your backend runs as a server (HTTP) ---
            const response = await fetch("http://localhost:5000/verify", {
                method: "POST",
                headers: { "Content-Type": "application/json" },
                body: JSON.stringify({ code: selection })
            });
            const result = await response.json() as { valid: boolean };

            if (result.valid) {
                vscode.window.showInformationMessage("✅ Code successfully validated!");
            } else {
                vscode.window.showErrorMessage("❌ Could not validate code.");
            }
        } catch (err: any) {
            vscode.window.showErrorMessage("Error talking to backend: " + err.message);
        }
    });

    context.subscriptions.push(disposable);
}

// Future use: run local Ocaml exe's depending on operating system
function runBackendProcess(code: string): Promise<{valid: boolean}> {
    return new Promise((resolve, reject) => {
        const proc = cp.spawn("path/to/ocaml/server", [], { stdio: ["pipe", "pipe", "inherit"] });
        proc.stdin.write(code);
        proc.stdin.end();

        let output = "";
        proc.stdout.on("data", data => output += data.toString());
        proc.on("close", () => {
            resolve({ valid: output.includes("success") });
        });
        proc.on("error", reject);
    });
}
