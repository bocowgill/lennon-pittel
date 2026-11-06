#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ $# -gt 1 || ($# -eq 1 && "$1" != --local-exports) ]]; then
  echo "Usage: $0 [--local-exports]" >&2
  exit 2
fi

prefix=$(lean --print-prefix)
verification_dir=$(mktemp -d "${TMPDIR:-/tmp}/lennon-pittel-comparator.XXXXXX")
trap 'rm -rf -- "$verification_dir"' EXIT
config="$verification_dir/comparator.json"
headline="LennonPittel.lennon_pittel_conjecture"

# Palomar installs the bundled checkers itself. Register them only in the local copy.
python3 - comparator.json "$config" "$prefix" "$headline" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix, headline = sys.argv[1:]
config = json.loads(Path(source).read_text(encoding="utf-8"))
expected = {
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": [headline],
}
if any(config.get(key) != value for key, value in expected.items()):
    raise SystemExit("Comparator configuration differs from the expected headline")
axioms = config.get("permitted_axioms", [])
if sorted(axioms) != ["Classical.choice", "Quot.sound", "propext"]:
    raise SystemExit("Comparator configuration must allow exactly the three standard axioms")
if config.get("definition_names") or "external_kernels" in config or "enable_nanoda" in config:
    raise SystemExit("Unexpected definition or kernel configuration in comparator.json")
config["external_kernels"] = {
    "nanoda": [str(Path(prefix, "bin", "nanoda_bin"))],
    "con-ron": [str(Path(prefix, "bin", "con-ron"))],
}
Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

if [[ $# -eq 0 ]]; then
  lake comparator --config "$config"
  exit
fi

# This mode is for a trusted local checkout on a host without bubblewrap.
# Challenge has one deliberate sorry. Build the actual proof with warnings as errors.
lake --wfail build Solution
lake build Challenge
targets=(
  Quot Quot.mk Quot.lift Quot.ind
  "$headline" propext Quot.sound Classical.choice
  Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight
  String.ofList Char.ofNat List eagerReduce Nat String String.mk Char
  optParam autoParam semiOutParam outParam
)
LEAN_ABORT_ON_PANIC=1 lake env leanexport Challenge -- "${targets[@]}" \
  > "$verification_dir/challenge.ndjson"
LEAN_ABORT_ON_PANIC=1 lake env leanexport Solution -- "${targets[@]}" \
  > "$verification_dir/solution.ndjson"

lake comparator --config "$config" \
  --challenge-from-export "$verification_dir/challenge.ndjson" \
  --solution-from-export "$verification_dir/solution.ndjson" \
  --inadvisably-no-sandbox
