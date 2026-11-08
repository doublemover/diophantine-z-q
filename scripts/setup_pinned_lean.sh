#!/usr/bin/env bash
# Tooling only. Never reads, installs or caches a project or Mathlib artifact.
set -euo pipefail
PIN=leanprover/lean4:v4.35.0
ELAN_SHA=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
export ELAN_HOME="$HOME/.elan"
ARCHIVE="$HOME/.cache/pinned-elan/4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz"
TOOLCHAIN="$ELAN_HOME/toolchains/leanprover--lean4---v4.35.0"
case "${1:-}" in
  installer)
    mkdir -p "$(dirname "$ARCHIVE")" "$RUNNER_TEMP/elan-install"
    if [[ ! -f "$ARCHIVE" ]]; then
      # Failed downloads never become cache entries; retries remain bounded.
      curl --fail --location --retry 3 --connect-timeout 30 --max-time 180 \
        -o "$ARCHIVE.partial" \
        https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz
      echo "$ELAN_SHA  $ARCHIVE.partial" | sha256sum --check -
      mv "$ARCHIVE.partial" "$ARCHIVE"
    fi
    echo "$ELAN_SHA  $ARCHIVE" | sha256sum --check -
    tar -xzf "$ARCHIVE" -C "$RUNNER_TEMP/elan-install"
    "$RUNNER_TEMP/elan-install/elan-init" -y --no-modify-path --default-toolchain none
    "$ELAN_HOME/bin/elan" --version | grep -E '^elan 4\.2\.4([[:space:]]|$)'
    echo "$ELAN_HOME/bin" >> "$GITHUB_PATH"
    ;;
  toolchain)
    # Reject changing a proof pin while silently restoring the old compiler.
    test "$(cat lean/lean-toolchain)" = "$PIN"
    test "$(cat quartics/quartic-318-326/proof/progress/lean-toolchain)" = "$PIN"
    if [[ ! -x "$TOOLCHAIN/bin/lean" ]]; then
      "$ELAN_HOME/bin/elan" toolchain install "$PIN"
    fi
    actual=$("$ELAN_HOME/bin/lean" "+$PIN" --version)
    [[ "$actual" == *'version 4.35.0,'* && "$actual" == *'eb6cafb'* ]]
    printf 'Verified pinned compiler: %s\n' "$actual"
    "$ELAN_HOME/bin/lake" "+$PIN" --version
    ;;
  *) echo 'Usage: setup_pinned_lean.sh installer|toolchain' >&2; exit 2 ;;
esac
