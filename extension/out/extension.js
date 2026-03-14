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
exports.deactivate = deactivate;
const vscode = __importStar(require("vscode"));
const statusBar_1 = require("./ui/statusBar");
const secrets_1 = require("./auth/secrets");
const network_1 = require("./api/network");
const outputChannel = vscode.window.createOutputChannel("Double-Checkk");
async function activate(context) {
    outputChannel.appendLine("Double-Checkk extension activating...");
    (0, statusBar_1.setupStatusBar)(context);
    context.subscriptions.push(vscode.commands.registerCommand("doublecheckk.configureApi", () => (0, secrets_1.configureApi)(context, outputChannel)), vscode.commands.registerCommand("doublecheckk.switchProvider", async () => {
        const cfg = vscode.workspace.getConfiguration("doublecheckk");
        const currentProvider = cfg.get("provider");
        const useEnv = cfg.get("useEnvFile");
        const selection = await vscode.window.showQuickPick([
            {
                label: "$(hubot) Change LLM Provider",
                description: `Currently using ${currentProvider}`,
                id: "change_provider",
            },
            {
                label: "$(key) Reset/Update API Key",
                description: "Overwrite existing global key",
                id: "reset_key",
            },
            {
                label: useEnv
                    ? "$(file-code) Disable .env Priority"
                    : "$(file-code) Enable .env Priority",
                id: "toggle_env",
            },
        ], { placeHolder: "Double-Checkk Settings" });
        if (!selection) {
            return;
        }
        if (selection.id === "change_provider") {
            const pick = await vscode.window.showQuickPick(secrets_1.PROVIDERS);
            if (pick) {
                await cfg.update("provider", pick.id, vscode.ConfigurationTarget.Global);
                vscode.window.showInformationMessage(`Switched to ${pick.label}`);
            }
        }
        else if (selection.id === "reset_key") {
            await (0, secrets_1.configureApi)(context, outputChannel);
        }
        else if (selection.id === "toggle_env") {
            await cfg.update("useEnvFile", !useEnv, vscode.ConfigurationTarget.Global);
            vscode.window.showInformationMessage(`.env priority is now ${!useEnv ? "Enabled" : "Disabled"}`);
        }
    }), vscode.commands.registerCommand("doublecheckk.verifySelection", async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor || !editor.selection) {
            vscode.window.showErrorMessage("No active editor or selection");
            return;
        }
        const selectionText = editor.document.getText(editor.selection);
        if (!selectionText.trim()) {
            vscode.window.showErrorMessage("Double-Checkk: Please select some C code to verify.");
            return;
        }
        const userGoal = await vscode.window.showInputBox({
            prompt: "What should this code do? (Leave blank for auto-inference)",
            placeHolder: "e.g. Ensure the result is non-negative",
        });
        if (userGoal === undefined) {
            return;
        } // User pressed Escape
        const creds = await (0, secrets_1.getProviderAndKey)(context, outputChannel);
        if (!creds) {
            return;
        }
        const cfg = vscode.workspace.getConfiguration("doublecheckk");
        const apiUrl = cfg.get("apiUrl");
        if (!apiUrl) {
            vscode.window.showErrorMessage("Double-Checkk: API URL is missing from settings.");
            return;
        }
        vscode.window.withProgress({
            location: vscode.ProgressLocation.Notification,
            title: "Double-Checkk: Formally verifying code...",
            cancellable: false,
        }, async () => {
            try {
                const result = await (0, network_1.verifyCodeOnCloud)(apiUrl, selectionText, creds.provider, creds.apiKey, userGoal || null);
                const action = await vscode.window.showInformationMessage(result.valid
                    ? "Code successfully validated"
                    : "Could not validate code.", "Show details");
                if (action === "Show details" && result.frama) {
                    const doc = await vscode.workspace.openTextDocument({
                        content: result.frama,
                        language: "c",
                    });
                    await vscode.window.showTextDocument(doc, { preview: true });
                    const replace = await vscode.window.showInformationMessage("Apply annotations?", "Replace selection", "Skip");
                    if (replace === "Replace selection") {
                        await editor.edit((ed) => ed.replace(editor.selection, result.frama));
                    }
                }
            }
            catch (err) {
                vscode.window.showErrorMessage(`Verification Error: ${err.message}`);
                outputChannel.appendLine(`[Error]: ${err.message}`);
            }
        });
    }));
    // QuickFix Code Action Provider
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
function deactivate() { }
//# sourceMappingURL=extension.js.map