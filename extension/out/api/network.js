"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.verifyCodeOnCloud = verifyCodeOnCloud;
async function verifyCodeOnCloud(apiUrl, code, provider, apiKey, userGoal) {
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
    return (await response.json());
}
//# sourceMappingURL=network.js.map