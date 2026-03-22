from fastapi import FastAPI, HTTPException, Security
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from typing import Optional
import frama_c  # Imports your existing frama_c.py script
import os
import uvicorn

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
        # Use the key the user entered in the UI
        final_api_key = user_provided_key
        provider = req.provider
    else:
        # 2. Key Rotation Logic
        fallback_keys_raw = os.environ.get("FALLBACK_GEMINI_KEYS", "")
        if not fallback_keys_raw:
            raise HTTPException(
                status_code=400,
                detail="No API key provided and no fallbacks available.",
            )

        key_pool = fallback_keys_raw.split(",")
        final_api_key = random.choice(
            key_pool
        )  # Randomly pick a key to distribute load
        provider = "gemini"  # Force the provider to gemini for fallbacks

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
