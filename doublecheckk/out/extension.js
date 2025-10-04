"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
const vscode = __importStar(require("vscode"));
const cp = __importStar(require("child_process")); // or use fetch if backend is HTTP
function activate(context) {
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
            const result = await response.json();
            if (result.valid) {
                vscode.window.showInformationMessage("✅ Code successfully validated!");
            }
            else {
                vscode.window.showErrorMessage("❌ Could not validate code.");
            }
        }
        catch (err) {
            vscode.window.showErrorMessage("Error talking to backend: " + err.message);
        }
    });
    context.subscriptions.push(disposable);
}
// Example helper if backend is a local process
function runBackendProcess(code) {
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
//# sourceMappingURL=extension.js.map