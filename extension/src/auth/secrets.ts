import * as vscode from "vscode";
import * as path from "path";
import * as fs from "fs";

export type ProviderId = "openai" | "anthropic" | "google";

export const PROVIDERS: { id: ProviderId; label: string }[] = [
  { id: "openai", label: "OpenAI (ChatGPT)" },
  { id: "anthropic", label: "Anthropic (Claude)" },
  { id: "google", label: "Google (Gemini)" },
];

export const secretKey = (p: ProviderId) => `doublecheckk.apiKey.${p}`;

export async function configureApi(
  context: vscode.ExtensionContext,
  outputChannel: vscode.OutputChannel,
): Promise<boolean> {
  const storagePick = await vscode.window.showQuickPick(
    [
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
    ],
    {
      placeHolder: "How would you like Double-Checkk to read your API key?",
      ignoreFocusOut: true,
    },
  );

  if (!storagePick) {
    return false;
  }

  const useEnv = storagePick.id === "env";
  const cfg = vscode.workspace.getConfiguration("doublecheckk");
  await cfg.update("useEnvFile", useEnv, vscode.ConfigurationTarget.Global);

  const providerPick = await vscode.window.showQuickPick(
    PROVIDERS.map((p) => ({ label: p.label, description: p.id, id: p.id })),
    { placeHolder: "Select your LLM provider", ignoreFocusOut: true },
  );

  if (!providerPick) {
    return false;
  }

  await cfg.update(
    "provider",
    providerPick.id,
    vscode.ConfigurationTarget.Global,
  );

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

    await context.secrets.store(
      secretKey(providerPick.id as ProviderId),
      apiKey,
    );
    vscode.window.showInformationMessage(
      `Double-Checkk: ${providerPick.label} API key saved securely.`,
    );
  } else {
    vscode.window.showInformationMessage(
      `Double-Checkk is configured to use a .env file. Ensure your ${providerPick.label} key is in your workspace!`,
    );
  }
  return true;
}

export async function getProviderAndKey(
  context: vscode.ExtensionContext,
  outputChannel: vscode.OutputChannel,
): Promise<{ provider: ProviderId; apiKey: string } | null> {
  const cfg = vscode.workspace.getConfiguration("doublecheckk");
  let provider = cfg.get<ProviderId>("provider", "openai");
  const useEnv = cfg.get<boolean>("useEnvFile", true);

  if (useEnv) {
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (workspaceFolders) {
      for (const folder of workspaceFolders) {
        const envPath = path.join(folder.uri.fsPath, ".env");
        if (fs.existsSync(envPath)) {
          try {
            const envContent = fs.readFileSync(envPath, "utf-8");
            let envKey = "";
            let foundProvider: ProviderId | null = null;

            for (const line of envContent.split("\n")) {
              const trimmed = line.trim();
              if (trimmed.startsWith("OPENAI_API_KEY=")) {
                envKey = trimmed.split("=", 2)[1];
                foundProvider = "openai";
              } else if (trimmed.startsWith("ANTHROPIC_API_KEY=")) {
                envKey = trimmed.split("=", 2)[1];
                foundProvider = "anthropic";
              } else if (trimmed.startsWith("GOOGLE_API_KEY=")) {
                envKey = trimmed.split("=", 2)[1];
                foundProvider = "google";
              }
            }

            if (envKey.trim() && foundProvider) {
              const userConsent = await vscode.window.showInformationMessage(
                `Double-Checkk found a ${foundProvider.toUpperCase()} API key in your workspace .env file. Allow?`,
                { modal: true },
                "Yes, allow",
                "No, ignore .env",
              );

              if (userConsent === "Yes, allow") {
                return { provider: foundProvider, apiKey: envKey.trim() };
              }
            }
          } catch (e) {
            outputChannel.appendLine(`Error reading .env file: ${e}`);
          }
        }
      }
    }
  }

  const newProvider = cfg.get<ProviderId>("provider", "openai");
  const newKey = await context.secrets.get(secretKey(newProvider));

  if (newKey) {
    return { provider: newProvider, apiKey: newKey };
  }

  vscode.window.showInformationMessage(
    "Double-Checkk: Let's get your API Key configured before verifying.",
  );
  const configured = await configureApi(context, outputChannel);

  // FIX: We must grab a FRESH snapshot of the config here because the old 'cfg' variable doesn't auto-update!
  const freshCfg = vscode.workspace.getConfiguration("doublecheckk");

  if (configured && !freshCfg.get<boolean>("useEnvFile")) {
    const freshProvider = freshCfg.get<ProviderId>("provider", "openai");
    const updatedKey = await context.secrets.get(secretKey(freshProvider));
    if (updatedKey) {
      return { provider: freshProvider, apiKey: updatedKey };
    }
  }

  vscode.window.showWarningMessage(
    "Double-Checkk: Verification cancelled. No API key configured.",
  );
  return null;
}
