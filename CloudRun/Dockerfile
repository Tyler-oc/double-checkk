# 1. Use a stable Ubuntu base (Debian/Ubuntu are best supported by OPAM)
FROM ubuntu:22.04

# 2. Prevent interactive prompts (like tzdata) from hanging the Docker build
ENV DEBIAN_FRONTEND=noninteractive

# 3. Install core system dependencies
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    build-essential \
    curl \
    git \
    m4 \
    unzip \
    pkg-config \
    libgmp-dev \
    z3 \
    python3 \
    python3-pip \
    opam \
    autoconf \
    graphviz \
    libgtk-3-dev \
    libgtksourceview-3.0-dev \
    && rm -rf /var/lib/apt/lists/*

# 4. Initialize OPAM 
RUN opam init --disable-sandboxing -y --auto-setup

# 5. Create the OCaml switch
RUN opam switch create 4.14.1 -y

# 6. Add OPAM binaries to the global PATH
ENV PATH="/root/.opam/4.14.1/bin:${PATH}"

# 7. Install Frama-C and the Alt-Ergo solver
RUN eval $(opam env) && \
    opam install -y alt-ergo frama-c && \
    why3 config --detect && \
    opam clean -a -c -s --logs

# 8. Set up your Python Cloud Run environment
WORKDIR /app

# Copy over your dependencies and install them
COPY requirements.txt .
RUN pip3 install --no-cache-dir -r requirements.txt

# Copy your Python handler, LLM script, and FastAPI web server
COPY . /app

# 9. Configure Cloud Run's required port
ENV PORT=8080
EXPOSE 8080

# 10. Boot up the API
CMD ["sh", "-c", "uvicorn main:app --host 0.0.0.0 --port ${PORT}"]