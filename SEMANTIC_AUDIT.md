# Dedicated DEST semantic audit (S1–S7)

**Status:** candidate formalization, not compiled in the authoring environment.
A green GitHub run is required. The mathematical construction in Hull.lean,
Matching.lean and Model.lean is unchanged. The existing Lean/mathlib v4.36.0
pin and five-lock replay are retained.

## Frozen independent reference

`DEST/ReferenceTheory.lean` imports Mathlib only. It defines first-order syntax
with equality and exactly two binary predicates. Variables are intrinsically
scoped (`Fin n`), with the most recently bound variable at index zero. Falsity,
implication and universal quantification form a classical basis; other
connectives are defined in that basis. All finite contexts, including the empty
parameter context, are permitted. `Formula.firstOnly` rejects every occurrence
of the second membership predicate, including below quantifiers. Renaming lifts
under binders; `eval_rename` and `eval_atVar` express capture avoidance.

`Axiom` is a predicate on CLOSED reference sentences. Its constructors are:

1. Extensionality for each membership separately.
2. Comprehension for every first-language formula with any finite number of
   parameters. No boundedness, stratification, positivity, or uniform-parameter
   restriction is imposed on comprehension.
3. Uniformity with uniform parameters. Its premise contains the literal
   corrected self-test `not φ(x, parameters)`. `self_test_correct` proves this
   is equivalent to `not m2 x x` in the presence of the extension equation.
   Empty parameter contexts satisfy the uniformity guard vacuously.
4. Existence of a first-membership empty set and least inductive set (an explicit
   infinity witness, also proved by the construction). Successor is specified
   by membership in the union of the predecessor and its singleton. These are
   first-language definitions, not additional primitive constants.
5. Natural induction on that first-membership least inductive set, for every
   formula of the FULL language with parameters. The schema quantifies over
   zero, omega, and the variables of the induction formula.
6. Full first-membership set induction, for every formula of the FULL language.
   This is stronger than transfinite induction restricted to first-membership
   ordinals; no second-membership well-foundedness is asserted.

The decisions in items 4–6 make explicit the interpretation of the original
informal induction clauses. The original user accepted capture-avoiding
substitution. The exact formalization of natural induction is an authoring
choice to be reviewed by the user. The reference theory includes infinity and
full first-membership set induction as a strengthening; satisfaction of that
strengthening also gives satisfaction of the corrected weaker theory.

## Formal checks and evidence

| Check | Principal theorem or evidence |
|---|---|
| S1 Language fidelity | `DESTReference.eval_rename`, `eval_atVar`, `DESTSemantic.first_language_translation` |
| S2 Axiom fidelity | `first_extensionality_correct`, `second_extensionality_correct`, `comprehension_correct`, `uniformity_correct`, `self_test_correct`, `model_satisfies_reference` |
| S3 Schema coverage | `unary_translation`, `eval_close`; arbitrarily many parameters and intrinsically scoped formulas |
| S4 One actual nonempty model | `DESTSemantic.exists_audited_model`, `exists_reference_model` |
| S5 Induction fidelity | `zero_correct`, `succ_correct`, `inductive_correct`, `omega_correct`, `setInduction_correct`, `model_satisfies_reference`; natural induction uses the same standard numerals and omega |
| S6 Assumptions | Strict axiom dependency audit of all listed theorem roots; source scan; frozen reference checksums |
| S7 Consistency bridge | `DESTReference.soundness`, `consistent_of_model`, `DESTSemantic.reference_consistent` |

S1/S3 prove translation of every well-scoped reference first-language formula
into the older construction's syntax. The older implementation also handles
ill-scoped indices by totalization; the reference theory does not require those
extra cases. S2 proves the intended semantic meaning of the closed sentences.
S4 requires the old ModelSpec and the independent reference theory in the same
existential witness, not in unrelated models. The generic reference endpoint
also supplies nonemptiness and well-foundedness explicitly.

## S7 scope: what is actually proved

`DEST/ReferenceLogic.lean` defines an explicit classical Hilbert calculus with
closed nonlogical axioms, propositional axioms and modus ponens, universal
instantiation and generalization, distribution/vacuity, and equality reflexivity
and replacement. Soundness is proved by induction on derivations. `Consistent`
means absence of a derivation of falsity in that declared calculus. No separate
completeness theorem for this calculus or equivalence with an external formal
calculus is asserted. Standard first-order soundness also applies externally to
the explicit nonempty model.

The formal endpoint is in Lean's classical foundations, not an arithmetization
of Con(ZFC) → Con(DEST). The ordinary ZFC construction is described in PROOF.md;
its interpretation and the natural-language-to-reference translation require
mathematical review. A hash freezes a selected reference version, but is not an
independent signature or a semantic oracle.

## Workflow

The standard build compiles all solution modules, including the reference and
semantic bridge modules, and the kernel reports are checked against the three
permitted axioms. `scripts/semantic_report.py` requires all expected reports
and the frozen reference checksums before writing `semantic-verdict.tsv`.
The report records completed formal obligations, not an automated judgment
about the original prose. The four comparator statement fixtures are separate
from the proof; no fixture is imported by Solution. The old endpoint plus
three new endpoints are all included in the focused proof export used by every
checker. The bridge and soundness proofs are their dependencies.

`PASS.txt` is created only after the baseline, semantic gate, and all five
locks succeed. A failing stage leaves no final PASS marker. Evidence is archived
on success or failure. The final report explicitly distinguishes the formal
semantic obligations from the outstanding human reference-specification review.
