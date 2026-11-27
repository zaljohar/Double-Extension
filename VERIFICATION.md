> Combined-extension notice: the focused checks below are retained. See
> [STRENGTH_AUDIT.md](STRENGTH_AUDIT.md) for the additional Z2-strength
> endpoints and their scope. The 52 frozen Comparator targets include the
> conditional exact Z2 equiconsistency theorem.

# Focused extension verification

`scripts/five-lock.sh` checks `baseline.sha256`, requires F1–F3 in `focused-verdict.tsv`, exports 52 theorem targets, and archives the focused proof and audit documentation. See FOCUSED_AUDIT.md for the scope of the focused checks.

---

# DEST semantic and five-lock verification

The repaired sources passed the native build and the source and axiom audits
in Lean and Mathlib v4.36.0.

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
and the standalone specification plus the independent reference logic, not the hull, matching, or model proof.
`Solution.lean` proves the exact same named claim using the original proofs.
`specification.sha256` records the frozen interface; do not alter it merely to
make a failing proof pass. The hash is an integrity baseline, not a signature
or protection from someone who can change the baseline itself. Review the
specification before treating it as the intended mathematical statement.

`Challenge.lean` supplies 52 independent theorem statements through placeholders.
`Solution.lean` and its proof dependencies exclude the challenge module. The
proof-source scan, axiom audit, and Comparator enforce the permitted axioms.

## Dedicated semantic gate

See `SEMANTIC_AUDIT.md`. The standard build must prove the semantic bridge,
reference-model existence, and soundness endpoints. Their axiom reports and
the reference checksums are mandatory. `semantic-verdict.tsv` is written only
when all expected formal obligations have acceptable kernel reports. The four
statement targets are matched by Comparator and exported together for the five
locks. Natural-language fidelity and the external ZFC interpretation still
require review; no green badge can by itself certify that review.

## Five locks

Lean and Mathlib are pinned to v4.36.0 for the bundled checkers.

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

The endpoints are semantic existence and syntactic consistency in the declared Hilbert calculus, in Lean's classical foundations. The ZFC
relative-consistency interpretation is described in PROOF.md, not separately
arithmetized in Lean. Even a green run does not automatically verify an arbitrary
informal interpretation of the specification.

## References for verification tooling

- https://github.com/leanprover/lean4/blob/v4.36.0/src/lake/Lake/CLI/Check.lean
- https://github.com/leanprover/lean4/blob/v4.36.0/src/lake/Lake/CLI/Help.lean
- https://github.com/leanprover/lean4export

### Obligation 3 update

See `WEAK_METATHEORY.md` for the fixed-fragment proof in the powerset-free metatheory. The new modules `WeakSpecification`, `WeakHull`, and `WeakFragment` construct actual finite-query hulls and prove the former `HullData`/`NatFrame` conditions, finite-fragment model existence with reflection, and ambient truth of first-language consequences. Two new Comparator endpoints and eleven axiom-audit entries are mandatory. The reflection statement guards the whole equivalence by support of the parameter list. The S resource proof and the published reductions are supplied as mathematical arguments.
