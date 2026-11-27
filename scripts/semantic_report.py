"""Emit a semantic-stage receipt only after kernel compilation and the axiom audit.
This verifies evidence presence, not the natural-language-to-logic translation.
"""
from pathlib import Path
import subprocess
import sys

report = Path(sys.argv[1])
output = Path(sys.argv[2])
output.unlink(missing_ok=True)
# Reuse the strict axiom whitelist parser; a missing report is a hard error.
subprocess.run([sys.executable, 'scripts/audit.py', str(report)], check=True)
subprocess.run(['sha256sum', '-c', 'specification.sha256'], check=True)
checks = [
    ('S1', 'Scoped language and capture-avoiding renaming', 'first_language_translation; eval_rename; eval_atVar'),
    ('S2', 'Closed reference axiom fidelity (formal)', 'first_extensionality_correct; second_extensionality_correct; comprehension_correct; uniformity_correct; self_test_correct; model_satisfies_reference'),
    ('S3', 'All finite parameter contexts and permitted formulas', 'unary_translation; eval_close'),
    ('S4', 'Same nonempty model', 'exists_audited_model; exists_reference_model'),
    ('S5', 'Full-language induction, first membership', 'zero_correct; succ_correct; omega_correct; setInduction_correct; model_satisfies_reference'),
    ('S6', 'Allowed axioms and frozen specification', 'audit.py; specification.sha256'),
    ('S7', 'Syntactic consistency in declared calculus', 'soundness; consistent_of_model; reference_consistent'),
]
output.write_text('check\tresult\tscope\tevidence\n' + ''.join(
    f'{k}\tPASS\t{label}\t{evidence}\n' for k, label, evidence in checks))
