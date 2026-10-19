#!/usr/bin/env python3
"""Compile a proposal folder the way the sextics verifier does, without the OS sandbox.

Usage: lean_compile.py SEXTICS_ROOT INSTANCE SUMMARY_FILE

Mirrors scripts/proposals/sandbox.py: builds HodgeComputer.Verify and the Mathlib modules the
proposal imports, writes HodgeTarget.lean from instance.rec, then compiles HodgeTarget, the
proposal modules in dependency order and HodgeChecked with `lean -o`. The summary file gets one
line per module and the full output of every module that failed or reported an error.
"""
import json
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import yaml

ROOT = Path(sys.argv[1]).resolve()
instance = sys.argv[2]
summary_path = Path(sys.argv[3])
sys.path.insert(0, str(ROOT / 'scripts/proposals'))
from acceptance import accepted_sources  # noqa: E402
from check import module_order, target_source  # noqa: E402

folder = ROOT / 'data' / instance
files = {name: (folder / name).read_bytes() for name in accepted_sources(folder)}
instance_rec = yaml.safe_load((folder / 'instance.rec').read_text())
manifest = json.loads(files['proof.json'])
order, imports = module_order(files)
print('module order:', order, flush=True)
print('external imports:', sorted(imports), flush=True)

lean_root = ROOT / 'formal/lean'
subprocess.run(['lake', 'build', 'HodgeComputer.Verify', *sorted(imports)], cwd=lean_root, check=True)
lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=lean_root).decode().strip()
prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=lean_root).decode().strip())
lean = prefix / 'bin/lean'
print(subprocess.check_output([str(lean), '--version']).decode().strip(), flush=True)

tmp = Path(tempfile.mkdtemp(prefix='hodge-compile-'))
src = tmp / 'source'
art = tmp / 'artifacts'
(src / 'Proposal').mkdir(parents=True)
(art / 'Proposal').mkdir(parents=True)
for name, raw in files.items():
    if name.endswith('.lean'):
        (src / 'Proposal' / name).write_bytes(raw)
(src / 'HodgeTarget.lean').write_text(target_source(instance_rec))
(src / 'HodgeChecked.lean').write_text(
    'import HodgeTarget\nimport Proposal.Solution\n'
    'theorem HodgeSubmission.checked : HodgeComputer.HasCertificate '
    'HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := ' + manifest['theorem'] + '\n')
print((src / 'HodgeTarget.lean').read_text(), flush=True)

env = dict(os.environ, LEAN_PATH=lean_path + ':' + str(art))
sequence = ['HodgeTarget.lean', *order, 'HodgeChecked.lean']
results = []
for name in sequence:
    rel = name if name in ('HodgeTarget.lean', 'HodgeChecked.lean') else 'Proposal/' + name
    out = art / rel.replace('.lean', '.olean')
    t0 = time.time()
    proc = subprocess.run([str(lean), '-j', '2', '-o', str(out), rel], cwd=src, env=env,
                          capture_output=True, text=True)
    dt = time.time() - t0
    log = proc.stdout + proc.stderr
    results.append((name, proc.returncode, dt, log))
    print(f'{name}: rc={proc.returncode} {dt:.0f}s', flush=True)
    if proc.returncode != 0:
        print(log[-20000:], flush=True)
        break

ok = all(rc == 0 for _, rc, _, _ in results) and len(results) == len(sequence)
with summary_path.open('w') as fh:
    fh.write(f'instance {instance}: {"ALL COMPILED" if ok else "FAILED"} '
             f'({len(results)}/{len(sequence)} modules attempted)\n')
    for name, rc, dt, _ in results:
        fh.write(f'{name}: rc={rc} {dt:.0f}s\n')
    for name, rc, dt, log in results:
        if rc != 0 or 'error' in log:
            fh.write(f'\n===== {name} (rc={rc}) =====\n{log[-40000:]}\n')
    warn = [(name, log.count('warning')) for name, rc, dt, log in results if 'warning' in log]
    if warn:
        fh.write('\nwarnings per module: ' + ', '.join(f'{n}:{c}' for n, c in warn) + '\n')
sys.exit(0 if ok else 1)
