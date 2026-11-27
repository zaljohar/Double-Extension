"""Require the actual new theorem dependency reports; no claims about ZF
object-language proof translations or internal arithmetized truth are made."""
from pathlib import Path
import subprocess
import sys

report, output = map(Path, sys.argv[1:])
output.unlink(missing_ok=True)
subprocess.run([sys.executable, 'scripts/audit.py', str(report)], check=True)
subprocess.run(['sha256sum', '-c', 'specification.sha256'], check=True)
rows = [
    ('F1', 'Infinity-free original specification, existence and uniformity of least inductive set', 'DESTOriginal.exists_original_model; DESTOriginal.exists_uniform_omega'),
    ('F2', 'Lean model existence for Original + SU1 + TI1; rank cut', 'DESTRank.exists_SU_TI_model'),
    ('F3', 'Single hereditarily uniform transitive Zermelo domain; full semantic axiom scheme', 'DESTOriginal.exists_hereditarily_uniform_Z_model; DESTOriginal.relativize_correct'),
]
output.write_text('check\tresult\tscope\tevidence\n' + ''.join(f'{k}\tPASS\t{s}\t{e}\n' for k,s,e in rows))
