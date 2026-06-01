FROM mcr.microsoft.com/devcontainers/base:bookworm

# Install dependencies needed by Lean / Mathlib tooling
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential \
    && rm -rf /var/lib/apt/lists/*

USER vscode
ENV ELAN_HOME=/home/vscode/.elan
ENV PATH=${ELAN_HOME}/bin:${PATH}

# Install elan (the Lean toolchain manager). The exact Lean version is taken
# from the project's lean-toolchain file when `lake` first runs.
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain none \
    && rm /tmp/elan-init.sh

WORKDIR /workspaces
