#!/bin/bash
# Regenerates MiniIMX93.lean from the Sockeye model sockeye/examples/mini_imx93.soc
# with Sockeye's Lean backend.
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
sockeye_dir="$script_dir/../../sockeye"

cd "$sockeye_dir"
cargo run --quiet -- -b lean --lean-prelude inline examples/mini_imx93.soc \
  -o "$script_dir/MiniIMX93.lean"
