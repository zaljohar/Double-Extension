#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Reject admitted proofs and custom axioms in the project source.
if grep -En '\b(sorry|admit|sorryAx)\b|^[[:space:]]*(axiom|constant)[[:space:]]' DEST.lean DEST/*.lean Solution.lean VerificationAudit.lean; then
  echo 'Forbidden proof placeholder or custom axiom found.' >&2
  exit 1
fi
lake build DEST Solution
{ lake env lean --trust=0 DEST/Audit.lean && lake env lean --trust=0 VerificationAudit.lean; } 2>&1 | tee axiom-audit.log
python3 scripts/audit.py axiom-audit.log
