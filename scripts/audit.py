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
for name in sorted({'DEST.' + x for x in expected} | {'DESTVerification.exists_model'}):
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
