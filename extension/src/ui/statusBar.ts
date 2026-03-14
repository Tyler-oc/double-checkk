import * as vscode from "vscode";

export function setupStatusBar(context: vscode.ExtensionContext) {
  const statusBarItem = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Right,
    100,
  );
  statusBarItem.command = "doublecheckk.switchProvider";
  context.subscriptions.push(statusBarItem);

  const updateStatusBar = () => {
    const provider = vscode.workspace
      .getConfiguration("doublecheckk")
      .get("provider", "openai");
    statusBarItem.text = `$(sparkle) Double-Checkk: ${String(provider).toUpperCase()}`;
    statusBarItem.show();
  };

  updateStatusBar();

  vscode.workspace.onDidChangeConfiguration((e) => {
    if (e.affectsConfiguration("doublecheckk")) {
      updateStatusBar();
    }
  });
}
