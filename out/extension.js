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
async function getPythonCommand() {
    for (const cmd of ["python3", "python"]) {
        try {
            cp.execSync(`${cmd} --version`, { stdio: "ignore" });
            return cmd;
        }
        catch {
            continue;
        }
    }
    throw new Error("Python not found. Please install Python 3.");
}
function commandExists(cmd) {
    try {
        cp.execSync(os_1.default.platform() === "win32" ? `where ${cmd}` : `command -v ${cmd}`, { stdio: "ignore" });
        return true;
    }
    catch {
        return false;
    }
}
async function installFrama() {
    if (commandExists("frama-c")) {
        return true;
    }
    const result = await vscode.window.showQuickPick(["Yes", "No"], {
        placeHolder: "Frama-C not found. Would you like to install it?",
    });
    if (result !== "Yes") {
        vscode.window.showInformationMessage("Installation cancelled. Frama-C is required.");
        return false;
    }
    const platform = os_1.default.platform();
    const terminal = vscode.window.createTerminal("Frama-C Installer");
    terminal.show();
    if (platform === "darwin") {
        if (!commandExists("brew")) {
            vscode.window.showErrorMessage("Homebrew is required on macOS.");
            return false;
        }
        terminal.sendText("brew update && brew install frama-c");
    }
    else if (platform === "linux") {
        if (commandExists("apt")) {
            terminal.sendText("sudo apt update && sudo apt install -y frama-c");
        }
        else if (commandExists("dnf")) {
            terminal.sendText("sudo dnf install -y frama-c");
        }
        else if (commandExists("pacman")) {
            terminal.sendText("sudo pacman -S --noconfirm frama-c");
        }
        else {
            vscode.window.showErrorMessage("Unsupported Linux package manager. Install frama-c manually.");
            return false;
        }
    }
    else {
        vscode.window.showErrorMessage("Frama-C requires Linux/WSL or macOS.");
        return false;
    }
    vscode.window.showInformationMessage("Check the terminal to complete Frama-C installation.");
    return true;
}
async function ensureDependencies(context) {
    const depsPath = path.join(context.globalStorageUri.fsPath, "python-deps");
    const flagFile = path.join(depsPath, ".installed");
    if (fs.existsSync(flagFile)) {
        return depsPath;
    }
    return await vscode.window.withProgress({
        location: vscode.ProgressLocation.Notification,
        title: "Installing Python dependencies...",
    }, async () => {
        if (!fs.existsSync(depsPath)) {
            fs.mkdirSync(depsPath, { recursive: true });
        }
        const reqPath = path.join(context.extensionPath, "requirements.txt");
        const pythonCmd = await getPythonCommand();
        await execPromise(`${pythonCmd} -m pip install -r "${reqPath}" --target "${depsPath}"`);
        fs.writeFileSync(flagFile, new Date().toISOString());
        return depsPath;
    });
}
async function configureApi(context) {
    const pick = await vscode.window.showQuickPick(PROVIDERS.map((p) => ({ label: p.label, description: p.id, id: p.id })), { placeHolder: "Select your LLM provider", ignoreFocusOut: true });
    if (!pick) {
        return false;
    }
    const apiKey = await vscode.window.showInputBox({
        prompt: `Enter API key for ${pick.label}`,
        password: true,
        ignoreFocusOut: true,
        validateInput: (v) => (v.trim() ? null : "API key cannot be empty"),
    });
    if (!apiKey) {
        return false;
    }
    await context.secrets.store(secretKey(pick.id), apiKey);
    await vscode.workspace
        .getConfiguration("doublecheckk")
        .update("provider", pick.id, vscode.ConfigurationTarget.Global);
    vscode.window.showInformationMessage(`${pick.label} API key saved.`);
    return true;
}
async function getProviderAndKey(context) {
    const cfg = vscode.workspace.getConfiguration("doublecheckk");
    let provider = cfg.get("provider", "openai");
    const useEnv = cfg.get("useEnvFile", true);
    if (useEnv) {
        const workspaceFolders = vscode.workspace.workspaceFolders;
        if (workspaceFolders) {
            for (const folder of workspaceFolders) {
                const envPath = path.join(folder.uri.fsPath, ".env");
                if (fs.existsSync(envPath)) {
                    try {
                        const envContent = fs.readFileSync(envPath, "utf-8");
                        const envLines = envContent.split("\n");
                        let envKey = "";
                        let foundProvider = null;
                        for (const line of envLines) {
                            const trimmed = line.trim();
                            if (trimmed.startsWith("OPENAI_API_KEY=")) {
                                envKey = trimmed.split("=", 2)[1];
                                foundProvider = "openai";
                            }
                            else if (trimmed.startsWith("ANTHROPIC_API_KEY=")) {
                                envKey = trimmed.split("=", 2)[1];
                                foundProvider = "anthropic";
                            }
                            else if (trimmed.startsWith("GOOGLE_API_KEY=")) {
                                envKey = trimmed.split("=", 2)[1];
                                foundProvider = "google";
                            }
                        }
                        if (envKey && foundProvider) {
                            outputChannel.appendLine(`Found API key for ${foundProvider} in .env file.`);
                            return { provider: foundProvider, apiKey: envKey.trim() };
                        }
                    }
                    catch (e) {
                        console.error("Error reading .env file:", e);
                        outputChannel.appendLine(`Error reading .env file: ${e}`);
                    }
                }
            }
        }
    }
    // Check API key in secrets fallback to config
    const apiKey = (await context.secrets.get(secretKey(provider))) ??
        cfg.get("apiKey");
    if (apiKey) {
        return { provider, apiKey };
    }
    // No key found. Prompt user.
    const selection = await vscode.window.showWarningMessage("Double-Checkk: No API key found. You must configure one to proceed.", "Configure API Key", "Cancel");
    if (selection === "Configure API Key") {
        const configured = await configureApi(context);
        if (configured) {
            return getProviderAndKey(context);
        }
        else {
            vscode.window.showInformationMessage("Double-Checkk: Configuration cancelled.");
            return null;
        }
    }
    return null;
}
let depsPathPromise;
async function activate(context) {
    outputChannel.appendLine("Double-Checkk extension activating...");
    depsPathPromise = ensureDependencies(context);
    installFrama();
    const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100);
    statusBarItem.command = "doublecheckk.switchProvider";
    context.subscriptions.push(statusBarItem);
    const updateStatusBar = () => {
        const provider = vscode.workspace.getConfiguration("doublecheckk").get("provider", "openai");
        statusBarItem.text = `$(sparkle) Double-Checkk: ${provider.toUpperCase()}`;
        statusBarItem.show();
    };
    updateStatusBar();
    vscode.workspace.onDidChangeConfiguration(e => {
        if (e.affectsConfiguration("doublecheckk"))
            updateStatusBar();
    });
    context.subscriptions.push(vscode.commands.registerCommand("doublecheckk.configureApi", async () => {
        await depsPathPromise;
        await configureApi(context);
    }), vscode.commands.registerCommand("doublecheckk.switchProvider", async () => {
        const cfg = vscode.workspace.getConfiguration("doublecheckk");
        const currentProvider = cfg.get("provider");
        const useEnv = cfg.get("useEnvFile");
        const options = [
            { label: "$(hubot) Change LLM Provider", description: `Currently using ${currentProvider}`, id: "change_provider" },
            { label: "$(key) Reset/Update API Key", description: "Overwrite existing global key", id: "reset_key" },
            { label: useEnv ? "$(file-code) Disable .env Priority" : "$(file-code) Enable .env Priority", id: "toggle_env" }
        ];
        const selection = await vscode.window.showQuickPick(options, {
            placeHolder: "Double-Checkk Settings"
        });
        if (!selection) {
            return;
        }
        if (selection.id === "change_provider") {
            // Re-use your existing configureApi logic or a simpler version:
            const pick = await vscode.window.showQuickPick(PROVIDERS);
            if (pick) {
                await cfg.update("provider", pick.id, vscode.ConfigurationTarget.Global);
                vscode.window.showInformationMessage(`Switched to ${pick.label}`);
            }
        }
        else if (selection.id === "reset_key") {
            await configureApi(context);
        }
        else if (selection.id === "toggle_env") {
            await cfg.update("useEnvFile", !useEnv, vscode.ConfigurationTarget.Global);
            vscode.window.showInformationMessage(`.env priority is now ${!useEnv ? "Enabled" : "Disabled"}`);
        }
    }));
    context.subscriptions.push(vscode.commands.registerCommand("doublecheckk.verifySelection", async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor || !editor.selection) {
            vscode.window.showErrorMessage("No active editor or selection");
            return;
        }
        const selection = editor.document.getText(editor.selection);
        if (!selection) {
            return;
        }
        const userGoal = await vscode.window.showInputBox({
            prompt: "What should this code do? (Leave blank for auto-inference)",
            placeHolder: "e.g. Ensure the result is non-negative",
        });
        const creds = await getProviderAndKey(context);
        if (!creds) {
            return;
        }
        vscode.window.showInformationMessage("Verifying selection...");
        try {
            const pyPath = context.asAbsolutePath(path.join("python_scripts", "frama_c.py"));
            const depsPath = await depsPathPromise;
            const result = await runPythonScript(pyPath, selection, creds.provider, creds.apiKey, depsPath, userGoal);
            const action = await vscode.window.showInformationMessage(result.valid
                ? "Code successfully validated"
                : "Could not validate code.", "Show details");
            if (action === "Show details") {
                const framaText = result.frama?.trim() || "// No Frama-C details returned.";
                const doc = await vscode.workspace.openTextDocument({
                    content: framaText,
                    language: "c",
                });
                await vscode.window.showTextDocument(doc, { preview: true });
                const replace = await vscode.window.showInformationMessage("Apply annotations?", "Replace selection", "Skip");
                if (replace === "Replace selection") {
                    await editor.edit((ed) => ed.replace(editor.selection, framaText));
                }
            }
        }
        catch (err) {
            vscode.window.showErrorMessage(`Error: ${err?.message ?? String(err)}`);
        }
    }));
    // Code Action Provider registration remains the same...
    context.subscriptions.push(vscode.languages.registerCodeActionsProvider({ scheme: "file" }, {
        provideCodeActions(doc, range) {
            if (range.isEmpty) {
                return;
            }
            const action = new vscode.CodeAction("Verify selection", vscode.CodeActionKind.QuickFix);
            action.command = {
                command: "doublecheckk.verifySelection",
                title: "Verify selection",
            };
            return [action];
        },
    }, { providedCodeActionKinds: [vscode.CodeActionKind.QuickFix] }));
}
async function runPythonScript(scriptPath, code, provider, apiKey, depsPath, userGoal) {
    const pythonCmd = await getPythonCommand();
    const pathSep = os_1.default.platform() === "win32" ? ";" : ":";
    // Merge PYTHONPATH properly
    const env = {
        ...process.env,
        PYTHONPATH: process.env.PYTHONPATH
            ? `${depsPath}${pathSep}${process.env.PYTHONPATH}`
            : depsPath,
    };
    return new Promise((resolve, reject) => {
        const args = [scriptPath, apiKey, provider];
        if (userGoal) {
            args.push(userGoal);
        }
        const proc = cp.spawn(pythonCmd, args, { env });
        proc.stdin.write(code);
        proc.stdin.end();
        let stdoutData = "";
        proc.stdout.on("data", (d) => (stdoutData += d.toString()));
        proc.stderr.on("data", (d) => outputChannel.append(`[Python Error]: ${d}`));
        proc.on("error", (err) => reject(new Error(`Process error: ${err.message}`)));
        proc.on("close", (code) => {
            try {
                const jsonMatch = stdoutData.match(/\{[\s\S]*\}/);
                if (!jsonMatch) {
                    throw new Error("Invalid response from script");
                }
                const parsed = JSON.parse(jsonMatch[0]);
                resolve({ valid: !!parsed.valid, frama: parsed.frama });
            }
            catch {
                resolve({ valid: /success/i.test(stdoutData) });
            }
        });
    });
}
//# sourceMappingURL=extension.js.map