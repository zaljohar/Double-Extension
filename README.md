# Double Extension Set Theory (DEST) — semantic and five-lock verification

Lean 4 formalization draft of the corrected double-extension theory and its
well-founded first-membership model. Pinned to Lean/mathlib v4.36.0 for the five-lock verification tools.

**Verification status (repair v2):** the supplied GitHub CI log reports successful
compilation of the core model and reference theory/logic under Lean 4.36.0.
The overall run stopped in the semantic bridge. This release addresses the
four reported semantic bridge errors; its new proofs have not yet been compiled.
The formal semantic audit and five locks remain pending a fresh CI run.
See `REPAIR_NOTES.md`.

## Main theorem

`DEST.exists_DEST_model` in `DEST/Model.lean`:

```lean
∃ r : Carrier → Carrier → Prop,
  IsDEST r ∧ WellFounded mem₁ ∧ Uniform r omegaObj ∧
    ∀ n : ℕ, Uniform r (numeral n)
```

`IsDEST` asserts first and second extensionality, comprehension for every
first-language formula and every finite parameter list, and uniformity for
comprehension with uniform parameters when the result is not a second-member
of itself. The second relation `r` is unrestricted except by these axioms.
`Uniform r a` means `∀ y, mem₁ y a ↔ r y a`. The syntax uses de Bruijn indices,
so the self-substitution in the corrected principle has no variable capture.
Quantifiers range over the actual carrier M, and atoms use actual first
membership. The finite-list semantics totalizes ill-scoped atoms to false;
every ordinary well-scoped first-order formula is covered by the grammar
(equality, membership, false, implication, universal quantification).

Separate theorems establish the natural-number structure and induction:
`omega_exact`, `omega_inductive`, `omega_least_inductive`, `numeral_injective`,
`natural_induction`, and `full_set_induction`. The latter works for arbitrary
predicates on the carrier, including interpretations of formulas using both
membership relations. It is not induction on the second membership relation.

## Organization

- `DEST/Syntax.lean`: first-language syntax and semantics, shared with the challenge.
- `DEST/Hull.lean`: countable witness hulls,
  elementarity, ambient representation of countable collections, and fresh points.
- `DEST/Matching.lean`: general countable back-and-forth lemma, proved by finite
  matching extensions and a union of a nested sequence.
- `DEST/Model.lean`: two hulls U ⊆ M, protected extensions, fixed/free extensions,
  matching, construction of second membership, verification, and induction.
- `DEST/Audit.lean`: explicit axiom reports for the main theorems.
- `PROOF.md`: mathematical proof, including the ordinary ZFC interpretation.

## Run on GitHub

1. Extract the full archive into the root of your repository and commit all files,
   including `.github/workflows/verify.yml`.
2. Open **Actions → DEST semantic and five-lock verification**. It runs on push and pull request;
   it may also be launched manually.
3. Inspect the standard build, axiom report, semantic audit and five locks. Download the
   `DEST-semantic-five-lock-verification-evidence` artifact. A successful run must include
   `PASS.txt`, `verdict.tsv`, `semantic-verdict.tsv`, comparator and individual kernel logs, the three
   NDJSON exports, and SHA-256 checksums. A failed run does not get a PASS marker.
4. The challenge fixture is deliberately incomplete: it states the obligation but
   is not proof code. Only `Challenge.lean` may contain its four statement-fixture placeholders;
   it is never imported by `Solution.lean`. The solution source scan and axiom
   audit disallow proof holes and nonstandard axioms.

Locally (Linux, with elan and bubblewrap installed):

```sh
lake update
lake exe cache get
bash scripts/five-lock.sh
```

The comparator uses all five bundled checker implementations plus Lean's default
kernel; the workflow also invokes the external checkers directly on the exact
same focused export. The only allowed foundational axioms are `propext`,
`Classical.choice`, and `Quot.sound`. See `VERIFICATION.md` for exact scope,
trust assumptions, and the frozen challenge statement.

## Meaning of relative consistency

The theorem is a semantic model-existence result in Lean's foundations, using
mathlib's `ZFSet` type. It does not encode ZFC's proof calculus or prove a
literal statement about arithmetic consistency predicates. The same construction
works in ordinary ZFC with the set-sized ambient V_{omega_1}, as explained in
`PROOF.md`. That is the mathematical relative-consistency argument. The precise
arithmetization of `Con(ZFC) → Con(DEST)` is not part of this draft.

## Independent semantic audit

Read `SEMANTIC_AUDIT.md` before treating a green run as evidence of fidelity to
DEST. The new files `DEST/ReferenceTheory.lean`, `DEST/ReferenceLogic.lean`, and
`DEST/SemanticAudit.lean` formalize a separate closed-sentence reference theory,
translation from every permitted formula, interpretation in the same model,
induction and a syntactic soundness bridge. `Solution.lean` adds three audited
endpoints without changing the original mathematical construction. Comparator
checks all four endpoint statements and all five locks replay their proof export.
The semantic report is mandatory, but natural-language specification review and
the external ZFC-relative interpretation remain human mathematical tasks.
