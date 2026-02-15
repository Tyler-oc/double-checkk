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
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.activate = activate;
const vscode = __importStar(require("vscode"));
const cp = __importStar(require("child_process"));
const path = __importStar(require("path"));
const fs = __importStar(require("fs"));
const util_1 = require("util");
const os_1 = __importDefault(require("os"));
const outputChannel = vscode.window.createOutputChannel("Python-debug");
const PROVIDERS = [
    { id: "openai", label: "OpenAI (ChatGPT)" },
    { id: "anthropic", label: "Anthropic (Claude)" },
    { id: "google", label: "Google (Gemini)" },
];
const secretKey = (p) => `doublecheckk.apiKey.${p}`;
const execPromise = (0, util_1.promisify)(cp.exec);
function commandExists(cmd) {
    try {
        cp.execSync(process.platform === "win32" ? `where ${cmd}` : `command -v ${cmd}`, {
            stdio: "ignore",
        });
        return true;
    }
    catch {
        return false;
    }
}
async function installFrama() {
    if (commandExists("frama-c")) {
        console.log("Frama-C already installed");
        return true;
    }
    const result = await vscode.window.showQuickPick(["Yes", "No"], {
        placeHolder: "Frama-C not found. Would you like to install it?",
    });
    // If user picks "No" or clicks away (undefined)
    if (result !== "Yes") {
        vscode.window.showInformationMessage("Installation cancelled. Frama-C is required for this feature.");
        return false; // This tells the caller to stop
    }
    const platform = os_1.default.platform();
    try {
        if (platform === "darwin") {
            if (!commandExists("brew"))
                throw new Error("Homebrew is required on macOS");
            cp.execSync("brew update && brew install frama-c", { stdio: "inherit" });
        }
        else if (platform === "linux") {
            if (commandExists("apt")) {
                cp.execSync("sudo apt update && sudo apt install -y frama-c", {
                    stdio: "inherit",
                });
            }
            else if (commandExists("dnf")) {
                cp.execSync("sudo dnf install -y frama-c", { stdio: "inherit" });
            }
            else if (commandExists("pacman")) {
                cp.execSync("sudo pacman -S --noconfirm frama-c", { stdio: "inherit" });
            }
            else {
                throw new Error("Unsupported Linux package manager. Please install frama-c manually.");
            }
        }
        else if (platform === "win32") {
            throw new Error("Frama-C is not officially supported on Windows. Use WSL (Ubuntu).");
        }
        else {
            throw new Error(`Unsupported platform: ${platform}`);
        }
        vscode.window.showInformationMessage("Frama-C installed successfully!");
        return true;
    }
    catch (err) {
        vscode.window.showErrorMessage(`Failed to install Frama-C: ${err instanceof Error ? err.message : err}`);
        return false;
    }
}
//download any dependencies the user doesn't have
async function ensureDependencies(context) {
    const depsPath = path.join(context.globalStorageUri.fsPath, "python-deps");
    const flagFile = path.join(depsPath, ".installed");
    if (fs.existsSync(flagFile)) {
        return depsPath;
    }
    return await vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Installing Python dependencies, please wait ...",
    }, async () => {
        try {
            // Create the directory if it doesn't exist
            if (!fs.existsSync(depsPath)) {
                fs.mkdirSync(depsPath, { recursive: true });
            }
            const requirementsPath = path.join(context.extensionPath, "requirements.txt");
            // Install dependencies
            const { stdout, stderr } = await execPromise(`pip install -r "${requirementsPath}" --target "${depsPath}"`);
            console.log("Pip stdout:", stdout);
            if (stderr) {
                console.log("Pip stderr:", stderr);
            }
            // Create flag file to mark successful installation
            fs.writeFileSync(flagFile, new Date().toISOString());
            return depsPath;
        }
        catch (error) {
            const errorMessage = error instanceof Error ? error.message : String(error);
            vscode.window.showErrorMessage(`Failed to install Python dependencies: ${errorMessage}`);
            throw error;
        }
    });
}
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
let depsPathPromise;
async function activate(context) {
    vscode.window.showInformationMessage("Double-Checkk extension activated");
    vscode.window.showInformationMessage("Verifying necessary package requirements");
    depsPathPromise = ensureDependencies(context);
    depsPathPromise.catch((err) => {
        console.error("Failed to install dependencies: ", err);
    });
    const framaInstalled = await installFrama();
    if (!framaInstalled) {
        return;
    }
    context.subscriptions.push(vscode.commands.registerCommand("doublecheckk.configureApi", async () => {
        const depsPath = await ensureDependencies(context);
        configureApi(context);
    }));
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
            const depsPath = await depsPathPromise;
            const result = await runPythonScript(pyPath, selection, creds.provider, creds.apiKey, depsPath);
            const action = await vscode.window.showInformationMessage(result.valid
                ? "Code successfully validated"
                : "Could not validate code.", "Show details");
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
function runPythonScript(scriptPath, code, provider, apiKey, depsPath) {
    if (!apiKey)
        throw new Error("API key not configured");
    const env = { ...process.env, PYTHONPATH: depsPath };
    return new Promise((resolve, reject) => {
        const proc = cp.spawn("python", [scriptPath, apiKey, provider], {
            stdio: ["pipe", "pipe", "pipe"],
            env: env,
        });
        // Write input to stdin
        proc.stdin.write(code);
        proc.stdin.end();
        let stdoutData = "";
        let stderrData = "";
        proc.stdout.on("data", (data) => {
            const str = data.toString();
            stdoutData += str;
            outputChannel.append(str);
        });
        proc.stderr?.on("data", (data) => {
            const str = data.toString();
            stderrData += str;
            outputChannel.append(`[STDERR]: ${str}`);
        });
        proc.on("error", (err) => {
            reject(new Error(`Failed to start Python process: ${err.message}`));
        });
        proc.on("close", (exitCode) => {
            if (exitCode !== 0) {
                console.error("Python script exited with code:", exitCode, stderrData);
                // Fallback: even if it failed, check if "success" was printed
                return resolve({ valid: /success/i.test(stdoutData) });
            }
            try {
                // Use regex to find the JSON block in case of leading/trailing junk text
                const jsonMatch = stdoutData.match(/\{[\s\S]*\}/);
                if (!jsonMatch) {
                    throw new Error("No JSON found in output");
                }
                const parsed = JSON.parse(jsonMatch[0]);
                resolve({
                    valid: Boolean(parsed.valid),
                    frama: typeof parsed.frama === "string" ? parsed.frama : undefined,
                });
            }
            catch (parseError) {
                console.warn("JSON parse failed, checking for keyword fallback...");
                // Final fallback to keyword detection if JSON is mangled
                resolve({ valid: /success/i.test(stdoutData) });
            }
        });
    });
}
//# sourceMappingURL=extension.js.map