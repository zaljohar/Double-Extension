# Z2 equiconsistency extension — audit boundary

The exact mathematical target is Con(original DEST) iff Con(Z2), and also
Con(original DEST + TI1) iff Con(Z2). It concerns neither SU1 nor the
Zermelo model extension. No Infinity field is added to Original.

See EXACT_STRENGTH_ARGUMENT.md for the complete proposed external proof using
Friedman (1981) and Kanovei–Lyubetsky (2025). The two published reductions are
not assumed as Lean axioms. They have not been formalized here.

| Stage | Formal scope | Status before CI |
|---|---|---|
| C0 | OriginalClosed, Original, and old BaseSatisfies have the same models; original + TI matches reference theory | Uncompiled |
| C1–C4 | Finite support, conditional matching and soundness, uniform comprehension and omega | Uncompiled |
| C5 | Internal weak-metatheory hull construction | Not formalized |
| C6a–C6g | Internal arithmetic, functional grammar, parameter-free comprehension and full induction, including the Infinity-free endpoint | Uncompiled |
| C6 external | Friedman restriction and Z2 interpretation of S | Not formalized |
| C7 | Exact consistency equivalence and arithmetic conservation, encoded provability | Not certified |

The new principal theorem `DESTOriginal.original_interprets_standard_arithmetic`
uses only the Original hypothesis. `DESTOriginalClosed.original_consistent`
is consistency in the declared sound calculus in Lean, not a weak-metatheory
consistency reduction. Do not infer exact proof-theoretic strength merely
from both theories having models in Lean's stronger metatheory.

The frozen independent Challenge contains 44 targets. All are required in
the export and axiom audit. A successful run may issue PASS.txt for those
actual targets only, with an explicit NOT KERNEL CERTIFIED qualification for
exact Z2 equiconsistency. No exact-strength certificate is produced.
