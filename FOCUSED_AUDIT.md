> Combined-extension notice: the focused checks below are retained. See
> [STRENGTH_AUDIT.md](STRENGTH_AUDIT.md) for the additional Z2-strength
> endpoints and their limitations. The full frozen Comparator list now has
> 44 targets. No exact-strength kernel certificate is issued.

# Focused extension: verification scope

The existing seven semantic checks and all five locks remain mandatory. Four new principal theorem statements are frozen in Challenge.lean and comparator.json, with proof dependencies audited under the same three permitted foundational axioms. The challenge fixture is never imported by the solution. `baseline.sha256` records the original ten Lean source hashes from the supplied green evidence.

| Check | Required evidence |
|---|---|
| F1 | `exists_original_model`, `original_of_reference`, `naturalF_correct`, `naturalF_firstOnly`, `uniform_collection`, `exists_uniform_omega`. Original has no Infinity field; the natural-number induction scheme is relational and ranges over actual first-order formulas. |
| F2 | `cut_witness`, `cut_subset_closed`, `cut_unrepresented_fresh`, `extension_assignment`, `subset_reflect`, `exists_SU_TI_model`. Same model, first-extension SU only, full first-membership TI. |
| F3 | `uniform_power`, `stages_exist`, `all_stages_good`, `stages_unique`, `stages_nested`, `relativize_correct`, `relativize_first`, `separation_in_domain`, `exists_hereditarily_uniform_Z_model`. A single transitive hereditarily uniform object, all Zermelo semantic axioms. |

Two explicit limitations are not certified by these automated checks:

1. The upper bound in ZF is the finite-fragment relative-consistency proof in FOCUSED_PROOF.md. The Lean rank model is a semantic existence theorem in Lean/Mathlib. No formal ZF proof-system translation or single global ZF interpretation is claimed.
2. The Zermelo endpoint verifies the entire external semantic scheme, with no ambient TI assumption. It is not a separate internal arithmetization of Zermelo satisfaction or Con(Z).

All new Lean sources are candidates awaiting ordinary Lean compilation. No local Lean installation or downloadable dependencies were available in the preparation environment. No PASS file for the new revision is distributed. GitHub must compile the new proofs, verify their dependencies, and run all five checkers before any green claim is justified. Human review of the specification and the external metatheoretic argument remains essential.
