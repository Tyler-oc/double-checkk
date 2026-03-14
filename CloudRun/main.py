from fastapi import FastAPI, HTTPException, Security
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from pydantic import BaseModel
from typing import Optional
import frama_c  # Imports your existing frama_c.py script
import os
import uvicorn

app = FastAPI(title="Double-Checkk Frama-C API")

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
    req: VerifyRequest, auth: HTTPAuthorizationCredentials = Security(security)
):
    if not req.code.strip():
        raise HTTPException(status_code=400, detail="C code cannot be empty")

    # Extract the key from the auth header
    api_key = auth.credentials

    if not api_key.strip():
        raise HTTPException(status_code=400, detail="API key is required")

    try:
        # Pass everything into your existing Frama-C logic
        result = frama_c.verify_c_code(
            user_code=req.code,
            user_api_key=api_key,
            api_provider=req.provider,
            user_goal=req.user_goal,
        )
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))


# We also add the port binding here just in case your Dockerfile CMD isn't handling it!
if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    uvicorn.run(app, host="0.0.0.0", port=port)
