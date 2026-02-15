import * as vscode from "vscode";
import * as cp from "child_process";
import * as path from "path";
import * as fs from "fs";
import { promisify } from "util";
import os from "os";

const outputChannel = vscode.window.createOutputChannel("Python-debug");

type ProviderId = "openai" | "anthropic" | "google";
const PROVIDERS: { id: ProviderId; label: string }[] = [
  { id: "openai", label: "OpenAI (ChatGPT)" },
  { id: "anthropic", label: "Anthropic (Claude)" },
  { id: "google", label: "Google (Gemini)" },
];

const secretKey = (p: ProviderId) => `doublecheckk.apiKey.${p}`;
const execPromise = promisify(cp.exec);

async function getPythonCommand(): Promise<string> {
  for (const cmd of ["python3", "python"]) {
    try {
      cp.execSync(`${cmd} --version`, { stdio: "ignore" });
      return cmd;
    } catch {
      continue;
    }
  }
  throw new Error("Python not found. Please install Python 3.");
}

function commandExists(cmd: string): boolean {
  try {
    cp.execSync(
      os.platform() === "win32" ? `where ${cmd}` : `command -v ${cmd}`,
      { stdio: "ignore" },
    );
    return true;
  } catch {
    return false;
  }
}

async function installFrama(): Promise<boolean> {
  if (commandExists("frama-c")) {
    return true;
  }

  const result = await vscode.window.showQuickPick(["Yes", "No"], {
    placeHolder: "Frama-C not found. Would you like to install it?",
  });

  if (result !== "Yes") {
    vscode.window.showInformationMessage(
      "Installation cancelled. Frama-C is required.",
    );
    return false;
  }

  const platform = os.platform();
  const terminal = vscode.window.createTerminal("Frama-C Installer");
  terminal.show();

  if (platform === "darwin") {
    if (!commandExists("brew")) {
      vscode.window.showErrorMessage("Homebrew is required on macOS.");
      return false;
    }
    terminal.sendText("brew update && brew install frama-c");
  } else if (platform === "linux") {
    if (commandExists("apt")) {
      terminal.sendText("sudo apt update && sudo apt install -y frama-c");
    } else if (commandExists("dnf")) {
      terminal.sendText("sudo dnf install -y frama-c");
    } else if (commandExists("pacman")) {
      terminal.sendText("sudo pacman -S --noconfirm frama-c");
    } else {
      vscode.window.showErrorMessage(
        "Unsupported Linux package manager. Install frama-c manually.",
      );
      return false;
    }
  } else {
    vscode.window.showErrorMessage("Frama-C requires Linux/WSL or macOS.");
    return false;
  }

  vscode.window.showInformationMessage(
    "Check the terminal to complete Frama-C installation.",
  );
  return true;
}

async function ensureDependencies(
  context: vscode.ExtensionContext,
): Promise<string> {
  const depsPath = path.join(context.globalStorageUri.fsPath, "python-deps");
  const flagFile = path.join(depsPath, ".installed");

  if (fs.existsSync(flagFile)) {
    return depsPath;
  }

  return await vscode.window.withProgress<string>(
    {
      location: vscode.ProgressLocation.Notification,
      title: "Installing Python dependencies...",
    },
    async () => {
      if (!fs.existsSync(depsPath)) {
        fs.mkdirSync(depsPath, { recursive: true });
      }
      const reqPath = path.join(context.extensionPath, "requirements.txt");

      const pythonCmd = await getPythonCommand();
      await execPromise(
        `${pythonCmd} -m pip install -r "${reqPath}" --target "${depsPath}"`,
      );

      fs.writeFileSync(flagFile, new Date().toISOString());
      return depsPath;
    },
  );
}

// --- KEEPING EXISTING API LOGIC ---
async function configureApi(context: vscode.ExtensionContext) {
  const pick = await vscode.window.showQuickPick(
    PROVIDERS.map((p) => ({ label: p.label, description: p.id, id: p.id })),
    { placeHolder: "Select your LLM provider", ignoreFocusOut: true },
  );
  if (!pick) {
    return;
  }

  const existing = await context.secrets.get(secretKey(pick.id));
  const apiKey = await vscode.window.showInputBox({
    prompt: `Enter API key for ${pick.label}`,
    value: existing ?? "",
    password: true,
    ignoreFocusOut: true,
    validateInput: (v) => (v.trim() ? null : "API key is required"),
  });
  if (!apiKey) {
    return;
  }

  await context.secrets.store(secretKey(pick.id), apiKey);
  await vscode.workspace
    .getConfiguration("doublecheckk")
    .update("provider", pick.id, vscode.ConfigurationTarget.Global);

  vscode.window.showInformationMessage(`${pick.label} API key saved.`);
}

async function getProviderAndKey(
  context: vscode.ExtensionContext,
  autoConfigure = true,
): Promise<{ provider: ProviderId; apiKey: string } | null> {
  const cfg = vscode.workspace.getConfiguration("doublecheckk");
  const provider = (cfg.get("provider") as ProviderId | undefined) ?? "openai";
  const apiKey =
    (await context.secrets.get(secretKey(provider))) ??
    (cfg.get("apiKey") as string | undefined);

  if (!apiKey) {
    if (autoConfigure) {
      await configureApi(context);
      return getProviderAndKey(context, false);
    }
    vscode.window.showWarningMessage("Double-Checkk: API key not configured.");
    return null;
  }
  return { provider, apiKey };
}

let depsPathPromise: Promise<string>;

export async function activate(context: vscode.ExtensionContext) {
  outputChannel.appendLine("Double-Checkk extension activating...");

  // Start background tasks
  depsPathPromise = ensureDependencies(context);

  // We check for Frama-C but don't let it block the whole activation
  installFrama();

  context.subscriptions.push(
    vscode.commands.registerCommand("doublecheckk.configureApi", async () => {
      await depsPathPromise;
      configureApi(context);
    }),
  );

  context.subscriptions.push(
    vscode.commands.registerCommand(
      "doublecheckk.verifySelection",
      async () => {
        const editor = vscode.window.activeTextEditor;
        if (!editor || !editor.selection) {
          vscode.window.showErrorMessage("No active editor or selection");
          return;
        }

        const selection = editor.document.getText(editor.selection);
        if (!selection) {
          return;
        }

        const creds = await getProviderAndKey(context, true);
        if (!creds) {
          return;
        }

        vscode.window.showInformationMessage("Verifying selection...");

        try {
          const pyPath = context.asAbsolutePath(
            path.join("python_scripts", "frama_c.py"),
          );
          const depsPath = await depsPathPromise;

          const result = await runPythonScript(
            pyPath,
            selection,
            creds.provider,
            creds.apiKey,
            depsPath,
          );

          const action = await vscode.window.showInformationMessage(
            result.valid
              ? "Code successfully validated"
              : "Could not validate code.",
            "Show details",
          );

          if (action === "Show details") {
            const framaText =
              result.frama?.trim() || "// No Frama-C details returned.";
            const doc = await vscode.workspace.openTextDocument({
              content: framaText,
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
                ed.replace(editor.selection, framaText),
              );
            }
          }
        } catch (err: any) {
          vscode.window.showErrorMessage(
            `Error: ${err?.message ?? String(err)}`,
          );
        }
      },
    ),
  );

  // Code Action Provider registration remains the same...
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

async function runPythonScript(
  scriptPath: string,
  code: string,
  provider: ProviderId,
  apiKey: string,
  depsPath: string,
): Promise<{ valid: boolean; frama?: string }> {
  const pythonCmd = await getPythonCommand();
  const pathSep = os.platform() === "win32" ? ";" : ":";

  // Merge PYTHONPATH properly
  const env = {
    ...process.env,
    PYTHONPATH: process.env.PYTHONPATH
      ? `${depsPath}${pathSep}${process.env.PYTHONPATH}`
      : depsPath,
  };

  return new Promise((resolve, reject) => {
    const proc = cp.spawn(pythonCmd, [scriptPath, apiKey, provider], { env });

    proc.stdin.write(code);
    proc.stdin.end();

    let stdoutData = "";
    proc.stdout.on("data", (d) => (stdoutData += d.toString()));
    proc.stderr.on("data", (d) => outputChannel.append(`[Python Error]: ${d}`));

    proc.on("error", (err) =>
      reject(new Error(`Process error: ${err.message}`)),
    );

    proc.on("close", (code) => {
      try {
        const jsonMatch = stdoutData.match(/\{[\s\S]*\}/);
        if (!jsonMatch) {
          throw new Error("Invalid response from script");
        }
        const parsed = JSON.parse(jsonMatch[0]);
        resolve({ valid: !!parsed.valid, frama: parsed.frama });
      } catch {
        resolve({ valid: /success/i.test(stdoutData) });
      }
    });
  });
}
