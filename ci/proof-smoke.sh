#!/usr/bin/env bash
set -euo pipefail

if [ -f "$HOME/.elan/env" ]; then
  # shellcheck disable=SC1090
  source "$HOME/.elan/env"
fi

lake build
lake exe domaintypedlispformalization
