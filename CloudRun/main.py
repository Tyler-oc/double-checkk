from fastapi import FastAPI, HTTPException, Security
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from typing import Optional
import frama_c
import os
import uvicorn
import itertools
from typing import List

app = FastAPI(title="Double-Checkk Frama-C API")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],  # This MUST include "OPTIONS" (which "*" does)
    allow_headers=["*"],
)

# This tells FastAPI to look for an "Authorization: Bearer <token>" header
security = HTTPBearer()


# We removed api_key from the JSON body model
class VerifyRequest(BaseModel):
    code: str
    provider: str
    user_goal: Optional[str] = None


def get_key_pool() -> List[str]:
    keys_raw = os.environ.get("FALLBACK_GEMINI_KEYS", "")
    return [key.strip() for key in keys_raw.split(",") if key.split()]


KEY_POOL = get_key_pool()

ROTATOR = itertools.cycle(KEY_POOL) if KEY_POOL else None


def get_next_fallback_key():
    if not ROTATOR:
        return None
    return next(ROTATOR)


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
        final_api_key = user_provided_key
        provider = req.provider
    else:
        final_api_key = get_next_fallback_key()
        if not final_api_key:
            raise HTTPException(
                status_code=400, detail="No key provided and no fallbacks configured."
            )
        provider = "gemini"
    try:
        # 3. Call your logic with the chosen key
        result = frama_c.verify_c_code(
            user_code=req.code,
            user_api_key=final_api_key,
            api_provider=provider,
            user_goal=req.user_goal,
        )
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


# We also add the port binding here just in case your Dockerfile CMD isn't handling it!
if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    uvicorn.run(app, host="0.0.0.0", port=port)
