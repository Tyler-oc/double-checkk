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
const cp = __importStar(require("child_process"));
const path = __importStar(require("path"));
const PROVIDERS = [
    { id: "openai", label: "OpenAI (ChatGPT)" },
    { id: "anthropic", label: "Anthropic (Claude)" },
    { id: "google", label: "Google (Gemini)" },
];
const secretKey = (p) => `doublecheckk.apiKey.${p}`;
async function configureApi(context) {
    const pick = await vscode.window.showQuickPick(PROVIDERS.map((p) => ({ label: p.label, description: p.id, id: p.id })), { placeHolder: "Select your LLM provider", ignoreFocusOut: true });
    if (!pick)
        return;
    const existing = await context.secrets.get(secretKey(pick.id));
    const apiKey = await vscode.window.showInputBox({
        prompt: `Enter API key for ${pick.label}`,
        value: existing ?? "",
        password: true,
        ignoreFocusOut: true,
        validateInput: (v) => (v.trim() ? null : "API key is required"),
    });
    if (!apiKey)
        return;
    await context.secrets.store(secretKey(pick.id), apiKey);
    await vscode.workspace
        .getConfiguration("doublecheckk")
        .update("provider", pick.id, vscode.ConfigurationTarget.Global);
    vscode.window.showInformationMessage(`${pick.label} API key saved.`);
}
async function getProviderAndKey(context, autoConfigure = true) {
    const cfg = vscode.workspace.getConfiguration("doublecheckk");
    const provider = cfg.get("provider") ?? "openai";
    const apiKey = (await context.secrets.get(secretKey(provider))) ??
        cfg.get("apiKey"); // legacy fallback
    if (!apiKey) {
        if (autoConfigure) {
            await configureApi(context);
            return getProviderAndKey(context, /*autoConfigure*/ false);
        }
        else {
            vscode.window.showWarningMessage("Double-Checkk: API key not configured.");
            return null;
        }
    }
    return { provider, apiKey };
}
function activate(context) {
    vscode.window.showInformationMessage("Double-Checkk extension activated");
    context.subscriptions.push(vscode.commands.registerCommand("doublecheckk.configureApi", () => configureApi(context)));
    context.subscriptions.push(vscode.commands.registerCommand("doublecheckk.verifySelection", async () => {
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
        const creds = await getProviderAndKey(context, /*autoConfigure*/ true);
        if (!creds)
            return;
        vscode.window.showInformationMessage("Verifying selection…");
        try {
            const pyPath = context.asAbsolutePath(path.join("python_scripts", "frama_c.py"));
            const result = await runPythonScript(pyPath, selection, creds.apiKey);
            const action = await vscode.window.showInformationMessage(result.valid
                ? "✅ Code successfully validated!"
                : "❌ Could not validate code.", "Show details");
            if (action === "Show details") {
                const framaText = result.frama && result.frama.trim().length > 0
                    ? result.frama
                    : "// No Frama-C details were returned by the verifier.";
                const doc = await vscode.workspace.openTextDocument({
                    content: framaText,
                    language: "c",
                });
                await vscode.window.showTextDocument(doc, { preview: true });
                const replace = await vscode.window.showInformationMessage("Replace the selected range with these annotations?", "Replace selection", "Skip");
                if (replace === "Replace selection") {
                    const originalRange = new vscode.Range(editor.selection.start, editor.selection.end);
                    await editor.edit((ed) => ed.replace(originalRange, framaText));
                }
            }
        }
        catch (err) {
            vscode.window.showErrorMessage("Error validating selection: " + (err?.message ?? String(err)));
        }
    }));
    context.subscriptions.push(vscode.languages.registerCodeActionsProvider({ scheme: "file" }, new (class {
        provideCodeActions(doc, range) {
            if (range.isEmpty)
                return;
            const action = new vscode.CodeAction("Verify selection", vscode.CodeActionKind.QuickFix);
            action.command = {
                command: "doublecheckk.verifySelection",
                title: "Verify selection",
            };
            return [action];
        }
    })(), { providedCodeActionKinds: [vscode.CodeActionKind.QuickFix] }));
}
function runPythonScript(scriptPath, code, apiKey) {
    if (!apiKey)
        throw new Error("API key not configured");
    return new Promise((resolve, reject) => {
        const proc = cp.spawn("python", [scriptPath, apiKey], {
            stdio: ["pipe", "pipe", "inherit"],
        });
        proc.stdin.write(code);
        proc.stdin.end();
        let output = "";
        proc.stdout.on("data", (data) => (output += data.toString()));
        proc.on("close", () => {
            try {
                const parsed = JSON.parse(output);
                resolve({
                    valid: !!parsed.valid,
                    frama: typeof parsed.frama === "string" ? parsed.frama : undefined,
                });
                return;
            }
            catch {
                resolve({ valid: /success/i.test(output) });
            }
        });
        proc.on("error", reject);
    });
}
//# sourceMappingURL=extension.js.map