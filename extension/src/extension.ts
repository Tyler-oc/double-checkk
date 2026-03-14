import * as vscode from "vscode";
import { setupStatusBar } from "./ui/statusBar";
import { configureApi, getProviderAndKey, PROVIDERS } from "./auth/secrets";
import { verifyCodeOnCloud } from "./api/network";

const outputChannel = vscode.window.createOutputChannel("Double-Checkk");

export async function activate(context: vscode.ExtensionContext) {
  outputChannel.appendLine("Double-Checkk extension activating...");

  setupStatusBar(context);

  context.subscriptions.push(
    vscode.commands.registerCommand("doublecheckk.configureApi", () =>
      configureApi(context, outputChannel),
    ),

    vscode.commands.registerCommand("doublecheckk.switchProvider", async () => {
      const cfg = vscode.workspace.getConfiguration("doublecheckk");
      const currentProvider = cfg.get("provider");
      const useEnv = cfg.get("useEnvFile");

      const selection = await vscode.window.showQuickPick(
        [
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
        ],
        { placeHolder: "Double-Checkk Settings" },
      );

      if (!selection) {
        return;
      }

      if (selection.id === "change_provider") {
        const pick = await vscode.window.showQuickPick(PROVIDERS);
        if (pick) {
          await cfg.update(
            "provider",
            pick.id,
            vscode.ConfigurationTarget.Global,
          );
          vscode.window.showInformationMessage(`Switched to ${pick.label}`);
        }
      } else if (selection.id === "reset_key") {
        await configureApi(context, outputChannel);
      } else if (selection.id === "toggle_env") {
        await cfg.update(
          "useEnvFile",
          !useEnv,
          vscode.ConfigurationTarget.Global,
        );
        vscode.window.showInformationMessage(
          `.env priority is now ${!useEnv ? "Enabled" : "Disabled"}`,
        );
      }
    }),

    vscode.commands.registerCommand(
      "doublecheckk.verifySelection",
      async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor || !editor.selection) {
          vscode.window.showErrorMessage("No active editor or selection");
          return;
        }

        const selectionText = editor.document.getText(editor.selection);
        if (!selectionText.trim()) {
          vscode.window.showErrorMessage(
            "Double-Checkk: Please select some C code to verify.",
          );
          return;
        }

        const userGoal = await vscode.window.showInputBox({
          prompt: "What should this code do? (Leave blank for auto-inference)",
          placeHolder: "e.g. Ensure the result is non-negative",
        });

        if (userGoal === undefined) {
          return;
        } // User pressed Escape

        const creds = await getProviderAndKey(context, outputChannel);
        if (!creds) {
          return;
        }

        const cfg = vscode.workspace.getConfiguration("doublecheckk");
        const apiUrl = cfg.get<string>("apiUrl");
        if (!apiUrl) {
          vscode.window.showErrorMessage(
            "Double-Checkk: API URL is missing from settings.",
          );
          return;
        }

        vscode.window.withProgress(
          {
            location: vscode.ProgressLocation.Notification,
            title: "Double-Checkk: Formally verifying code...",
            cancellable: false,
          },
          async () => {
            try {
              const result = await verifyCodeOnCloud(
                apiUrl,
                selectionText,
                creds.provider,
                creds.apiKey,
                userGoal || null,
              );

              const action = await vscode.window.showInformationMessage(
                result.valid
                  ? "Code successfully validated"
                  : "Could not validate code.",
                "Show details",
              );

              if (action === "Show details" && result.frama) {
                const doc = await vscode.workspace.openTextDocument({
                  content: result.frama,
                  language: "c",
                });
                await vscode.window.showTextDocument(doc, { preview: true });

                const replace = await vscode.window.showInformationMessage(
                  "Apply annotations?",
                  "Replace selection",
                  "Skip",
                );
                if (replace === "Replace selection") {
                  await editor.edit((ed) =>
                    ed.replace(editor.selection, result.frama!),
                  );
                }
              }
            } catch (err: any) {
              vscode.window.showErrorMessage(
                `Verification Error: ${err.message}`,
              );
              outputChannel.appendLine(`[Error]: ${err.message}`);
            }
          },
        );
      },
    ),
  );

  // QuickFix Code Action Provider
  context.subscriptions.push(
    vscode.languages.registerCodeActionsProvider(
      { scheme: "file" },
      {
        provideCodeActions(doc, range) {
          if (range.isEmpty) {
            return;
          }
          const action = new vscode.CodeAction(
            "Verify selection",
            vscode.CodeActionKind.QuickFix,
          );
          action.command = {
            command: "doublecheckk.verifySelection",
            title: "Verify selection",
          };
          return [action];
        },
      },
      { providedCodeActionKinds: [vscode.CodeActionKind.QuickFix] },
    ),
  );
}

export function deactivate() {}
