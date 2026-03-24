from fastapi import FastAPI, HTTPException, Security
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from typing import Optional
import frama_c
import os
import uvicorn
import threading
from typing import List

app = FastAPI(title="Double-Checkk Frama-C API")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],  # This MUST include "OPTIONS" (which "*" does)
    allow_headers=["*"],
)

security = HTTPBearer()


class VerifyRequest(BaseModel):
    code: str
    provider: str
    user_goal: Optional[str] = None


def get_key_pool() -> List[str]:
    keys_raw = os.environ.get("FALLBACK_GEMINI_KEYS", "")
    return [key.strip() for key in keys_raw.split(",") if key.strip()]


KEY_POOL = get_key_pool()

_key_index = 0
_key_lock = threading.Lock()


def get_fallback_keys_in_order() -> List[str]:
    """Returns all fallback keys starting from the current round-robin position."""
    global _key_index
    if not KEY_POOL:
        return []
    with _key_lock:
        start = _key_index
        _key_index = (_key_index + 1) % len(KEY_POOL)
    return [KEY_POOL[(start + i) % len(KEY_POOL)] for i in range(len(KEY_POOL))]


@app.get("/health")
def health_check():
    return {"status": "Frama-C API is running"}


@app.post("/verify")
def verify_endpoint(
    req: VerifyRequest,
    auth: Optional[HTTPAuthorizationCredentials] = Security(security),
):
    user_provided_key = auth.credentials if auth else None

    if user_provided_key and user_provided_key.strip() != "FALLBACK":
        # User-provided key: single attempt, no fallback pool available
        try:
            result = frama_c.verify_c_code(
                user_code=req.code,
                user_api_key=user_provided_key,
                api_provider=req.provider,
                user_goal=req.user_goal,
            )
            if result.get("api_error"):
                raise HTTPException(
                    status_code=401,
                    detail="The provided API key failed. Please verify your key and try again.",
                )
            return result
        except HTTPException:
            raise
        except Exception as e:
            raise HTTPException(status_code=500, detail=str(e))
    else:
        # Fallback pool: try each key in round-robin order until one works
        keys = get_fallback_keys_in_order()
        if not keys:
            raise HTTPException(
                status_code=400, detail="No key provided and no fallbacks configured."
            )

        last_detail = "All fallback keys exhausted without a successful response."
        for key in keys:
            try:
                result = frama_c.verify_c_code(
                    user_code=req.code,
                    user_api_key=key,
                    api_provider="gemini",
                    user_goal=req.user_goal,
                )
                if result.get("api_error"):
                    last_detail = result.get("error", "API key did not respond.")
                    continue
                return result
            except Exception as e:
                last_detail = str(e)
                continue

        raise HTTPException(
            status_code=503,
            detail=f"All fallback API keys failed. Last error: {last_detail}",
        )


# We also add the port binding here just in case your Dockerfile CMD isn't handling it!
if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    uvicorn.run(app, host="0.0.0.0", port=port)
