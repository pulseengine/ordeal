#!/usr/bin/env bash
# Install varve the VERIFIED way (varve's own README, "Install varve"): the
# release's SHA256SUMS.txt is cosign-verified against varve's release
# workflow identity BEFORE install.sh is checked against it and run — never
# a naked `curl | sh` from a branch. Then install the layer pinned in
# ./varve.toml (realm + trust root from ./varve-realms.toml) and put the
# pinned tools on PATH.
#
#   scripts/install_varve.sh            # in CI: also appends to $GITHUB_PATH
#
# Needs: curl, cosign, sha256sum (or shasum). Pins a varve version when
# VARVE_VERSION is set (e.g. v0.38.0); otherwise the latest release — the
# layer pin in varve.toml is what fixes the TOOL versions either way.
set -euo pipefail

if [ -n "${VARVE_VERSION:-}" ]; then
  B="https://github.com/pulseengine/varve/releases/download/${VARVE_VERSION}"
else
  B="https://github.com/pulseengine/varve/releases/latest/download"
fi
W=$(mktemp -d)
( cd "$W"
  curl -fsSLO "$B/install.sh"
  curl -fsSLO "$B/SHA256SUMS.txt"
  curl -fsSLO "$B/SHA256SUMS.txt.cosign.bundle"
  cosign verify-blob \
    --bundle SHA256SUMS.txt.cosign.bundle \
    --certificate-identity-regexp '^https://github\.com/pulseengine/varve/\.github/workflows/release\.yml@' \
    --certificate-oidc-issuer https://token.actions.githubusercontent.com \
    SHA256SUMS.txt
  if command -v sha256sum >/dev/null; then
    grep ' \./install\.sh$' SHA256SUMS.txt | sha256sum -c -
  else
    grep ' \./install\.sh$' SHA256SUMS.txt | shasum -a 256 -c -
  fi
  sh install.sh )

VARVE="${VARVE_INSTALL_DIR:-$HOME/.varve/bin}/varve"
"$VARVE" --version
# Installing the varve BINARY is not installing the LAYER (gale's lesson).
"$VARVE" install
"$VARVE" shim install
if [ -n "${GITHUB_PATH:-}" ]; then
  # Shims first, so `rivet` resolves to the pinned layer, not a runner tool.
  echo "${VARVE_ROOT:-$HOME/.varve}/shims" >> "$GITHUB_PATH"
  echo "${VARVE_INSTALL_DIR:-$HOME/.varve/bin}" >> "$GITHUB_PATH"
fi
"$VARVE" which rivet
