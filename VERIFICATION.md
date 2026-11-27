# DEST five-lock verification

**Status at packaging:** source and configuration prepared; no Lean executable
or network to install Lean/mathlib was available in the authoring container.
No successful build, comparator verdict, or external-kernel run is claimed.

## Frozen target

`DESTVerification.exists_model` in `Challenge.lean` requires an actual domain
of ZFSet objects, a second membership relation, standard numerals and an omega
object, satisfying `DESTVerification.ModelSpec` in `DEST/Specification.lean`.
The first membership is inherited from ZFSet. The four corrected DEST axioms,
first-membership well-foundedness, uniformity of omega and the numerals,
injective numerals, zero, successor, exact omega membership, inductiveness,
least inductive set, natural induction and full first-membership set induction
are all conjuncts in the SAME existential model. The last two quantify over
all predicates on the domain and thus cover formulas involving both relations.
This is not a claim about induction along the second membership relation.

`DEST/Syntax.lean` contains the original first-language grammar/semantics,
extracted unchanged from `Hull.lean`. The challenge imports only this syntax
and the standalone specification, not the hull, matching, or model proof.
`Solution.lean` proves the exact same named claim using the original proofs.
`specification.sha256` records the frozen interface; do not alter it merely to
make a failing proof pass. The hash is an integrity baseline, not a signature
or protection from someone who can change the baseline itself. Review the
specification before treating it as the intended mathematical statement.

`Challenge.lean` has one deliberate `sorry` as a comparator statement fixture.
It must never be imported by the solution or used to prove anything. It is not
an admitted proof in the model construction. The proof-source scan, axiom audit,
and Comparator independently enforce the permitted axiom list on the solution.

## Five locks

Pinned Lean and Mathlib: v4.36.0 (upgraded from v4.29.0 to obtain the bundled
checkers). The original hull, matching and model proof bodies have not been
ported or tested against the new version; API repairs may be needed.

Baseline: project build with `--trust=0`, source scan and axiom audit. All model
and induction theorem reports must be present. No custom axioms are permitted.

1. `lake comparator --paranoid` compares the challenge and proof exports, checks
   their axiom dependencies, and runs the native kernel and all five bundled
   checkers. The script requires the affirmative verdict from every checker.
2. `leanchecker-paranoid --from-export` checks the focused proof directly.
3. `con-leche --verified --jobs=1` checks the same proof directly.
4. `con-ron --verified --jobs=1` checks the same proof directly.
5. `nanoda_bin` (strict permitted-axiom configuration) and
   `lean4lean --import` both check the same proof directly.

All commands must exit successfully; bash pipefail is enabled, and there is no
continue-on-error. The `Proof.ndjson` file is a byte-for-byte copy of the focused
`Solution.ndjson` checked by Comparator and by the direct checkers. The challenge
export is for statement matching only, never a proof. Each export is hashed and
verified before and after checking. Logs and the resolved dependency manifest
are archived. The script also records hashes of the checker executables and
source files. Direct replay runs in the trusted checkout, outside the Comparator
sandbox. This workflow assumes trusted repository source and dependencies;
it is not a sandbox for adversarial code. By default Comparator's sandbox is
enabled. On a trusted checkout only, a manual workflow dispatch can explicitly
opt out if the runner cannot create namespaces. Such a run is marked REDUCED
ISOLATION; do not represent it as a sandboxed verification.

The endpoint is semantic existence in Lean's classical foundations. The ZFC
relative-consistency interpretation is described in PROOF.md, not separately
arithmetized in Lean. Even a green run does not automatically verify an arbitrary
informal interpretation of the specification.

## References for verification tooling

- https://github.com/leanprover/lean4/blob/v4.36.0/src/lake/Lake/CLI/Check.lean
- https://github.com/leanprover/lean4/blob/v4.36.0/src/lake/Lake/CLI/Help.lean
- https://github.com/leanprover/lean4export
