"""Audit proof presence and frozen statements; do not certify external bridges."""
from pathlib import Path
import subprocess
import sys
report, out = map(Path, sys.argv[1:])
out.unlink(missing_ok=True)
subprocess.run([sys.executable, 'scripts/audit.py', str(report)], check=True)
subprocess.run(['sha256sum', '-c', 'specification.sha256'], check=True)
subprocess.run(['sha256sum', '-c', 'baseline.sha256'], check=True)
rows = [
    ('C0', 'PASS', 'Closed original axioms without Infinity equivalent to Original and earlier base; original + TI equivalent to full reference; original closed soundness'),
    ('C1', 'PASS', 'First-only formulas independent of second relation; exact finite proof support'),
    ('C2', 'PASS', 'Finite fragment matching and satisfaction, CONDITIONAL on HullData and NatFrame'),
    ('C3', 'PASS', 'Uniform comprehension, internal uniform omega, numeric-parameter comprehension in base-theory models'),
    ('C4', 'PASS', 'Finite-fragment model existence implies consistency, CONDITIONAL'),
    ('C5', 'NOT_FORMALIZED', 'Weak set-theory proof of hull existence and arithmetic absoluteness'),
    ('C6a', 'PASS', 'Arbitrary guarded number and real quantifier translation and first-language fidelity'),
    ('C6b', 'PASS', 'Parameter-free comprehension and full induction in the guarded language'),
    ('C6c', 'PASS', 'Internal zero and successor laws, transitivity and predecessor in arbitrary base models'),
    ('C6d', 'PASS', 'Internal recursion graphs, uniqueness, and PA operation laws for arbitrary base models'),
    ('C6e', 'PASS', 'Relational arithmetic grammar, first-only translation, parameter-free comprehension and induction'),
    ('C6f', 'PASS', 'Standard two-sorted functional syntax, PA operations, comprehension and induction'),
    ('C6g', 'PASS', 'Infinity-free original theory has internal parameter-free functional arithmetic model'),
    ('C6', 'PARTIAL', 'Internal parameter-free arithmetic model checked; Friedman and weak set-theory interpretation are not formalized'),
    ('C7', 'NOT_CERTIFIED', 'Exact equiconsistency and arithmetic conservativity')
]
out.write_text('check\tresult\tscope\n' + ''.join('\t'.join(r)+'\n' for r in rows))
