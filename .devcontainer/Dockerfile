FROM mcr.microsoft.com/devcontainers/base:bookworm

# Install dependencies needed by Lean / Mathlib tooling
RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get install -y --no-install-recommends \
        curl git ca-certificates build-essential \
    && rm -rf /var/lib/apt/lists/*

USER vscode
ENV ELAN_HOME=/home/vscode/.elan
ENV PATH=${ELAN_HOME}/bin:${PATH}

# Install elan (the Lean toolchain manager).
RUN curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain none \
    && rm /tmp/elan-init.sh

# Bake the Lean toolchain into the image (a deterministic, network-only download,
# so it belongs in an image layer rather than postCreateCommand). The build
# context is the repo root (see devcontainer.json `build.context`), keeping
# `lean-toolchain` as the single source of truth for the version.
COPY --chown=vscode lean-toolchain /tmp/lean-toolchain
RUN elan toolchain install "$(cat /tmp/lean-toolchain)" \
    && elan default "$(cat /tmp/lean-toolchain)" \
    && rm /tmp/lean-toolchain

WORKDIR /workspaces
