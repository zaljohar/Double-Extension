# Repair v1 — first native build errors

Based on the reported Lean 4.36.0 CI failure in `DEST/Model.lean` at lines 67 and 360.

- Explicitly type the projection on the target subtype `↥Defs` in the countability proof, preventing the elaborator from selecting the source subtype.
- Establish `P (numeral n)` for all `n : ℕ` before introducing the arbitrary member of omega; this prevents a dependent membership hypothesis from being generalized into the induction hypothesis.

All theorem statements, reference axioms, comparator targets, semantic checks, and verification workflows are unchanged from the semantic-five-lock release. The original log lists only the four earlier specification checksums; this full release includes the two additional reference files and their checksums. Replace the previous repository contents with this release, including hidden `.github` files.

Validation: archive integrity, specification checksums, and script syntax only. No Lean executable is available in the local preparation environment; native compilation, semantic proofs, and independent checker runs are not yet verified.
