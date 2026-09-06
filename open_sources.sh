#!/usr/bin/env bash
set -euo pipefail

# Load only the parent library heap. Every theory of this project is source-loaded.
SIGMOID_PROJECT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
exec /home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle jedit \
  -n -l Real_and_Complex_Analytic -i Sigmoid_Universal_Approximation \
  -d /home/dusty/Desktop/Isabelle/afp-2026-04-09/thys/Smooth_Manifolds \
  -d '/home/dusty/Desktop/Real and Complex Analytic' \
  -d "$SIGMOID_PROJECT_DIR" \
  -j -noserver -j -norestore "$SIGMOID_PROJECT_DIR"/*.thy
