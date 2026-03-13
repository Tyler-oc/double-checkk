from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from typing import Optional
import frama_c  # Imports your existing frama_c.py script

app = FastAPI(title="Double-Checkk Frama-C API")


# Define the expected JSON payload
class VerifyRequest(BaseModel):
    code: str
    provider: str
    api_key: str
    user_goal: Optional[str] = None


@app.get("/health")
def health_check():
    return {"status": "Frama-C API is running"}


@app.post("/verify")
def verify_endpoint(req: VerifyRequest):
    if not req.code.strip():
        raise HTTPException(status_code=400, detail="C code cannot be empty")

    if not req.api_key.strip():
        raise HTTPException(status_code=400, detail="API key is required")

    try:
        # Call your existing logic directly
        result = frama_c.verify_c_code(
            user_code=req.code,
            user_api_key=req.api_key,
            api_provider=req.provider,
            user_goal=req.user_goal,
        )
        return result
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
