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
exports.secretKey = exports.PROVIDERS = void 0;
exports.configureApi = configureApi;
exports.getProviderAndKey = getProviderAndKey;
const vscode = __importStar(require("vscode"));
const path = __importStar(require("path"));
const fs = __importStar(require("fs"));
exports.PROVIDERS = [
    { id: "openai", label: "OpenAI (ChatGPT)" },
    { id: "anthropic", label: "Anthropic (Claude)" },
    { id: "google", label: "Google (Gemini)" },
];
const secretKey = (p) => `doublecheckk.apiKey.${p}`;
exports.secretKey = secretKey;
async function configureApi(context, outputChannel) {
    const storagePick = await vscode.window.showQuickPick([
        {
            label: "$(shield) Enter a Global API Key",
            description: "Save securely in VS Code's secret storage",
            id: "global",
        },
        {
            label: "$(file-code) Use Workspace .env File",
            description: "Read the key automatically from your project's .env file",
            id: "env",
        },
    ], {
        placeHolder: "How would you like Double-Checkk to read your API key?",
        ignoreFocusOut: true,
    });
    if (!storagePick) {
        return false;
    }
    const useEnv = storagePick.id === "env";
    const cfg = vscode.workspace.getConfiguration("doublecheckk");
    await cfg.update("useEnvFile", useEnv, vscode.ConfigurationTarget.Global);
    const providerPick = await vscode.window.showQuickPick(exports.PROVIDERS.map((p) => ({ label: p.label, description: p.id, id: p.id })), { placeHolder: "Select your LLM provider", ignoreFocusOut: true });
    if (!providerPick) {
        return false;
    }
    await cfg.update("provider", providerPick.id, vscode.ConfigurationTarget.Global);
    if (!useEnv) {
        const apiKey = await vscode.window.showInputBox({
            prompt: `Enter API key for ${providerPick.label}`,
            password: true,
            ignoreFocusOut: true,
            validateInput: (v) => (v.trim() ? null : "API key cannot be empty"),
        });
        if (!apiKey) {
            return false;
        }
        await context.secrets.store((0, exports.secretKey)(providerPick.id), apiKey);
        vscode.window.showInformationMessage(`Double-Checkk: ${providerPick.label} API key saved securely.`);
    }
    else {
        vscode.window.showInformationMessage(`Double-Checkk is configured to use a .env file. Ensure your ${providerPick.label} key is in your workspace!`);
    }
    return true;
}
async function getProviderAndKey(context, outputChannel) {
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
                        let envKey = "";
                        let foundProvider = null;
                        for (const line of envContent.split("\n")) {
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
                        if (envKey.trim() && foundProvider) {
                            const userConsent = await vscode.window.showInformationMessage(`Double-Checkk found a ${foundProvider.toUpperCase()} API key in your workspace .env file. Allow?`, { modal: true }, "Yes, allow", "No, ignore .env");
                            if (userConsent === "Yes, allow") {
                                return { provider: foundProvider, apiKey: envKey.trim() };
                            }
                        }
                    }
                    catch (e) {
                        outputChannel.appendLine(`Error reading .env file: ${e}`);
                    }
                }
            }
        }
    }
    const newProvider = cfg.get("provider", "openai");
    const newKey = await context.secrets.get((0, exports.secretKey)(newProvider));
    if (newKey) {
        return { provider: newProvider, apiKey: newKey };
    }
    vscode.window.showInformationMessage("Double-Checkk: Let's get your API Key configured before verifying.");
    const configured = await configureApi(context, outputChannel);
    // FIX: We must grab a FRESH snapshot of the config here because the old 'cfg' variable doesn't auto-update!
    const freshCfg = vscode.workspace.getConfiguration("doublecheckk");
    if (configured && !freshCfg.get("useEnvFile")) {
        const freshProvider = freshCfg.get("provider", "openai");
        const updatedKey = await context.secrets.get((0, exports.secretKey)(freshProvider));
        if (updatedKey) {
            return { provider: freshProvider, apiKey: updatedKey };
        }
    }
    vscode.window.showWarningMessage("Double-Checkk: Verification cancelled. No API key configured.");
    return null;
}
//# sourceMappingURL=secrets.js.map