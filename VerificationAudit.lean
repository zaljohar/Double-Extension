import Solution

#print axioms DESTVerification.exists_model

#print axioms DESTSemantic.first_language_translation
#print axioms DESTSemantic.unary_translation
#print axioms DESTReference.eval_rename
#print axioms DESTReference.eval_atVar
#print axioms DESTReference.eval_close
#print axioms DESTSemantic.self_test_correct
#print axioms DESTSemantic.extension_correct
#print axioms DESTSemantic.allUniform_correct
#print axioms DESTSemantic.zero_correct
#print axioms DESTSemantic.succ_correct
#print axioms DESTSemantic.inductive_correct
#print axioms DESTSemantic.omega_correct
#print axioms DESTSemantic.model_satisfies_reference
#print axioms DESTReference.soundness
#print axioms DESTReference.consistent_of_model
#print axioms DESTSemantic.exists_audited_model
#print axioms DESTSemantic.exists_reference_model
#print axioms DESTSemantic.reference_consistent
#print axioms DESTSemantic.first_extensionality_correct
#print axioms DESTSemantic.second_extensionality_correct
#print axioms DESTSemantic.comprehension_correct
#print axioms DESTSemantic.uniformity_correct
#print axioms DESTSemantic.setInduction_correct

-- Focused extension: Infinity-free specification and its derived omega.
#print axioms DESTOriginal.exists_original_model
#print axioms DESTOriginal.original_of_reference
#print axioms DESTOriginal.naturalF_correct
#print axioms DESTOriginal.naturalF_firstOnly
#print axioms DESTOriginal.uniform_collection
#print axioms DESTOriginal.exists_uniform_omega

-- Rank cut, back-and-forth, and first-extension subset closure.
#print axioms DESTRank.cut_witness
#print axioms DESTRank.cut_subset_closed
#print axioms DESTRank.cut_unrepresented_fresh
#print axioms DESTRank.extension_assignment
#print axioms DESTRank.subset_reflect
#print axioms DESTRank.exists_SU_TI_model

-- Internal powerset towers and full semantic Separation.
#print axioms DESTOriginal.uniform_power
#print axioms DESTOriginal.stages_exist
#print axioms DESTOriginal.all_stages_good
#print axioms DESTOriginal.stages_unique
#print axioms DESTOriginal.stages_nested
#print axioms DESTOriginal.relativize_correct
#print axioms DESTOriginal.relativize_first
#print axioms DESTOriginal.separation_in_domain
#print axioms DESTOriginal.exists_hereditarily_uniform_Z_model

#print axioms DESTStrength.first_only_eval
#print axioms DESTStrength.finite_assignment
#print axioms DESTStrength.finite_model_of_hull
#print axioms DESTStrength.uniform_comprehension_of_model
#print axioms DESTStrength.finite_proof_support
#print axioms DESTStrength.consistent_of_fragments
#print axioms DESTStrength.uniform_omega_of_model
#print axioms DESTStrength.number_comprehension_of_model

#print axioms DESTArithmetic.firstOnly_rename
#print axioms DESTArithmetic.eval_swapHead
#print axioms DESTArithmetic.subsetF_correct
#print axioms DESTArithmetic.guarded_firstOnly
#print axioms DESTArithmetic.guarded_translation_correct
#print axioms DESTArithmetic.guarded_number_comprehension
#print axioms DESTArithmetic.internal_induction
#print axioms DESTArithmetic.guarded_induction
#print axioms DESTArithmetic.internal_successor_laws

#print axioms DESTArithmetic.addF_correct
#print axioms DESTArithmetic.mulF_correct
#print axioms DESTArithmetic.internal_recursion_graph
#print axioms DESTArithmetic.internal_recursion_unique
#print axioms DESTArithmetic.internal_arithmetic_laws
#print axioms DESTArithmetic.arithmetic_firstOnly
#print axioms DESTArithmetic.arithmetic_translation_correct
#print axioms DESTArithmetic.parameter_free_arithmetic
#print axioms DESTArithmetic.base_interprets_arithmetic

#print axioms DESTArithmetic.term_graph_correct
#print axioms DESTArithmetic.standard_translation_correct
#print axioms DESTArithmetic.standard_arithmetic_model
#print axioms DESTArithmetic.base_interprets_standard_arithmetic

-- Bridge to the Infinity-free specification
#print axioms DESTOriginal.base_of_original
#print axioms DESTOriginal.original_of_base
#print axioms DESTOriginal.original_iff_base
#print axioms DESTOriginal.original_TI_iff_reference
#print axioms DESTOriginal.original_interprets_standard_arithmetic

-- Independent closed-sentence Infinity-free theory
#print axioms DESTOriginalClosed.natural_correct
#print axioms DESTOriginalClosed.induction_correct
#print axioms DESTOriginalClosed.consistent_of_original_model
#print axioms DESTOriginalClosed.satisfies_iff_original
#print axioms DESTOriginalClosed.satisfies_iff_base
#print axioms DESTOriginalClosed.original_consistent
