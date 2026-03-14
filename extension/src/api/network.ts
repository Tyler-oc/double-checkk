import { ProviderId } from "../auth/secrets";

export async function verifyCodeOnCloud(
  apiUrl: string,
  code: string,
  provider: ProviderId,
  apiKey: string,
  userGoal: string | null,
): Promise<{ valid: boolean; frama?: string }> {
  const response = await fetch(apiUrl, {
    method: "POST",
    headers: {
      "Content-Type": "application/json",
      Authorization: `Bearer ${apiKey}`,
    },
    body: JSON.stringify({
      code: code,
      provider: provider,
      user_goal: userGoal,
    }),
  });

  if (!response.ok) {
    const errorText = await response.text();
    throw new Error(`Server returned ${response.status}: ${errorText}`);
  }

  return (await response.json()) as { valid: boolean; frama?: string };
}
