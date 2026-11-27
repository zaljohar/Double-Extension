"""Fail closed unless all expected theorem axiom reports are present and safe."""
import pathlib
import re
import sys

report = pathlib.Path(sys.argv[1]).read_text()
expected = {
    'countable_matching', 'hull_elementary', 'countable_represented',
    'extension_assignment', 'exists_DEST_model', 'full_set_induction',
    'omega_exact', 'omega_inductive', 'omega_least_inductive',
    'natural_induction', 'numeral_injective',
}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
semantic = {
    'DESTSemantic.first_extensionality_correct',
    'DESTSemantic.second_extensionality_correct',
    'DESTSemantic.comprehension_correct',
    'DESTSemantic.uniformity_correct',
    'DESTSemantic.setInduction_correct',

    'DESTSemantic.first_language_translation', 'DESTSemantic.unary_translation',
    'DESTReference.eval_rename', 'DESTReference.eval_atVar', 'DESTReference.eval_close',
    'DESTSemantic.self_test_correct', 'DESTSemantic.extension_correct',
    'DESTSemantic.allUniform_correct', 'DESTSemantic.zero_correct',
    'DESTSemantic.succ_correct', 'DESTSemantic.inductive_correct', 'DESTSemantic.omega_correct',
    'DESTSemantic.model_satisfies_reference', 'DESTReference.soundness',
    'DESTReference.consistent_of_model', 'DESTSemantic.exists_audited_model',
    'DESTSemantic.exists_reference_model', 'DESTSemantic.reference_consistent',
}
for name in sorted({'DEST.' + x for x in expected} | {'DESTVerification.exists_model'} | semantic):
    pattern = rf"['`]?{re.escape(name)}['`]?\s+depends on axioms:\s*\[([^\]]*)\]"
    match = re.search(pattern, report, re.S)
    if match:
        deps = {x.strip().strip("'`") for x in match[1].split(',') if x.strip()}
        extra = deps - allowed
        if extra:
            raise SystemExit(f'{name}: unexpected axiom dependencies: {sorted(extra)}')
        print(f'{name}: {sorted(deps)}')
    elif re.search(rf"['`]?{re.escape(name)}['`]?\s+does not depend on any axioms", report):
        print(f'{name}: no axioms')
    else:
        raise SystemExit(f'Missing axiom report for {name}')
print('PASS: every expected theorem has an acceptable axiom report.')
