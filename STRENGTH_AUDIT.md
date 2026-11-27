# Exact Z2 equiconsistency audit

`DESTExact.z2_equiconsistency` proves the equivalence of Henkin model existence
for Z2, original corrected DEST, and corrected DEST with first-membership set
induction. The original closed DEST axioms use the Infinity-free formulation.

| Check | Formal scope |
|---|---|
| C0–C5 | Closed original axioms and their equivalences, finite proof support, and the earlier construction over Lean's ZFSet |
| C5S | Set-coded finite-fragment models in arbitrary powerset-free set models with the constructible-cut resources, and truth transfer for first-language theorems |
| C6a–C6g | Standard functional arithmetic, parameter-free impredicative comprehension, and full induction in corrected DEST |
| C6 | Two explicit hypotheses giving the model-level consequences of Friedman and Kanovei–Lyubetsky |
| C7 | Conditional full model-existence equivalence, via first-order compactness |
| C8 | From a Z2 model and the constructible interpretation, syntactic consistency of both DEST calculi |
| C9 | Ordinary first-order completeness gives external equiconsistency. The arithmetic-consequence comparison has its own written proof. |

The new proof constructs graphs and induction counterexamples as sets of the
weak model. Its only use of a finite list of formulas comes from outside
that model. `DESTSet.first_sentence_of_internal_model` treats each actual
derivation by extracting its finite axiom support.

The six new targets bring the total to 52. The audit accepts only Lean's
standard foundational axioms. The two published results are hypotheses of
the theorem. See [the mathematical argument](EXACT_STRENGTH_ARGUMENT.md) and
[the recorded verdict](five-lock-evidence/PASS.txt).
