#!/usr/bin/env bash
# Run on a clean trusted checkout with Lean/mathlib v4.36.0 installed.
set -euo pipefail
cd "$(dirname "$0")/.."
export LEAN_ABORT_ON_PANIC=1
export LC_ALL=C.UTF-8
out="$PWD/five-lock-evidence"
mkdir -p "$out"
rm -f "$out"/{PASS.txt,verdict.tsv,SHA256SUMS,tool-binaries.sha256}
exec > >(tee "$out/run.log") 2>&1
printf 'lock\tresult\n' > "$out/verdict.tsv"
record() { printf '%s\t%s\n' "$1" "$2" | tee -a "$out/verdict.tsv"; }
trap 'rc=$?; if ((rc != 0)); then echo "FAILED (exit $rc); see logs; no PASS marker"; fi' EXIT

sha256sum -c specification.sha256
# Ensure none of the independent tools can silently be omitted.
lean --version | tee "$out/toolchain.txt"
grep -F 'version 4.36.0' "$out/toolchain.txt"
lake --version | tee -a "$out/toolchain.txt"
prefix="$(lean --print-prefix)"
for bin in leanexport leanchecker leanchecker-paranoid con-leche con-ron nanoda_bin lean4lean; do
  test -x "$prefix/bin/$bin" || { echo "Missing bundled checker: $bin"; exit 1; }
  sha256sum "$prefix/bin/$bin" >> "$out/tool-binaries.sha256"
done
cp lean-toolchain lakefile.toml lake-manifest.json comparator.json specification.sha256 "$out/"
sha256sum DEST.lean DEST/*.lean Solution.lean Challenge.lean VerificationAudit.lean scripts/*.sh scripts/*.py .github/workflows/verify.yml > "$out/source.sha256"
git rev-parse HEAD > "$out/git-commit.txt" 2>/dev/null || printf 'not a git checkout\n' > "$out/git-commit.txt"

bash scripts/verify.sh 2>&1 | tee "$out/native-build-and-audit.log"
cp axiom-audit.log "$out/"
record 'Standard Lean (--trust=0) and axiom audit' PASS

# Challenge is a statement fixture, not a proof module. It is never imported
# by Solution. The only intentional hole is in Challenge.lean.
lake build Challenge Solution 2>&1 | tee "$out/challenge-build.log"
# Same focused root set used by Lean 4.36.0 Lake comparator (including the
# primitive kernel names and the permitted axioms).
targets=(Quot Quot.mk Quot.lift Quot.ind DESTVerification.exists_model
  propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd
  Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft
  Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String
  String.mk Char optParam autoParam semiOutParam outParam)
for mod in Challenge Solution; do
  lake env leanexport "$mod" -- "${targets[@]}" > "$out/$mod.ndjson" 2> "$out/$mod-export.log"
  test -s "$out/$mod.ndjson"
done
# This is the exact focused proof export that all checkers will receive.
cp "$out/Solution.ndjson" "$out/Proof.ndjson"
(cd "$out" && sha256sum Challenge.ndjson Solution.ndjson Proof.ndjson > SHA256SUMS && sha256sum -c SHA256SUMS)

# Keep sandboxing enabled by default. A reduced-isolation run is possible only
# with explicit opt-in, and is never described as sandboxed in its evidence.
args=()
if [[ "${DEST_ALLOW_NO_SANDBOX:-0}" == 1 ]]; then
  args+=(--inadvisably-no-sandbox)
  printf 'REDUCED ISOLATION: explicitly opted out of Comparator sandbox\n' > "$out/isolation.txt"
else
  command -v bwrap >/dev/null
  printf 'Comparator sandbox enabled (exports built in trusted checkout)\n' > "$out/isolation.txt"
fi
cat "$out/isolation.txt"
lake comparator --config=comparator.json \
  --challenge-from-export="$out/Challenge.ndjson" \
  --solution-from-export="$out/Proof.ndjson" \
  --paranoid "${args[@]}" 2>&1 | tee "$out/comparator.log"
# In addition to the process exit code, require affirmative reports for every
# bundled checker, so skipped or unavailable kernels never count as success.
for kernel in 'Lean default' 'Lean paranoid' con-leche con-ron nanoda lean4lean; do
  grep -Fx "$kernel kernel accepts the solution" "$out/comparator.log"
done
grep -Fx 'Your solution is okay!' "$out/comparator.log"
record '1 Comparator + Mathlib (statement match and axiom whitelist)' PASS
# Replay the same export directly. Explicit verified mode for con-leche and
# con-ron; strict permitted-axiom checking for NanoDa.
proof="$out/Proof.ndjson"
lake env leanchecker-paranoid --from-export "$proof" 2>&1 | tee "$out/lock2-paranoid.log"
record '2 leanchecker-paranoid' PASS
lake env con-leche --verified --jobs=1 "$proof" 2>&1 | tee "$out/lock3-con-leche.log"
record '3 con-leche' PASS
lake env con-ron --verified --jobs=1 "$proof" 2>&1 | tee "$out/lock4-con-ron.log"
record '4 con-ron' PASS
python3 - "$proof" "$out/nanoda.json" <<'PY'
import json, sys
from pathlib import Path
Path(sys.argv[2]).write_text(json.dumps({
    'use_stdin': False, 'export_file_path': sys.argv[1],
    'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
    'unpermitted_axiom_hard_error': True, 'num_threads': 2,
    'nat_extension': True, 'string_extension': True}, indent=2) + '\n')
PY
lake env nanoda_bin "$out/nanoda.json" 2>&1 | tee "$out/lock5-nanoda.log"
lake env lean4lean --import "$proof" 2>&1 | tee "$out/lock5-lean4lean.log"
record '5 NanoDa + lean4lean' PASS
(cd "$out" && sha256sum -c SHA256SUMS)
sha256sum -c "$out/source.sha256"
sha256sum -c specification.sha256
printf 'Standard Lean: PASS\nFive locks: 5/5 PASS\n' | tee "$out/PASS.txt"
cat "$out/isolation.txt" >> "$out/PASS.txt"
if [[ -n "${GITHUB_STEP_SUMMARY:-}" ]]; then
  { echo '### DEST verification'; echo '```'; cat "$out/PASS.txt" "$out/verdict.tsv"; echo '```'; } >> "$GITHUB_STEP_SUMMARY"
fi
