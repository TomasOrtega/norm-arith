"""Compile exploratory reviewed edits; this does not freeze benchmark evidence."""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'scripts'))
from benchmark import prepare_sources, run_process, require_success, edited_source_setups
from verify_selection import compile_selected

parser = argparse.ArgumentParser()
parser.add_argument('--manifest', type=Path, default=Path(__file__).with_name('manifest.json'))
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--path', action='append', help='compile all current edits in only this file')
args = parser.parse_args()
output = args.output.resolve()
if output.exists():
    raise SystemExit('output must be new')
output.mkdir(parents=True)
manifest_bytes = args.manifest.read_bytes()
manifest = json.loads(manifest_bytes)
if args.path:
    selected = set(args.path)
    manifest['files'] = [row for row in manifest['files'] if row['path'] in selected]
    manifest['candidates'] = [row for row in manifest['candidates'] if row['path'] in selected]
(output/'input-manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n')
mathlib = ROOT / '.lake/packages/mathlib'
prepared, accounting = prepare_sources(manifest, mathlib)
for row in prepared:
    path = output/'sources'/row['path']
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(row['replacement'])
setups = {}
for row in prepared:
    module = row['path'][:-5].replace('/', '.')
    path = ROOT/'.lake/census-full-v3/setups'/f'{module}.json.gz'
    setups[row['path']] = json.loads(gzip.decompress(path.read_bytes()))
records = []
def command(label, argv):
    if Path(argv[0]).name == 'lake' and argv[1] == 'setup-file':
        argv = [argv[0], '--no-build', *argv[1:]]
    result = run_process(argv, ROOT, output/'setup'/label, 600)
    records.append(result)
    require_success(result)
    return (Path(result['log_dir'])/'stdout.log').read_text()
lean = shutil.which('lean')
patched, setup_records = edited_source_setups(
    {row['path']: output/'sources'/row['path'] for row in prepared},
    mathlib=mathlib, lean=lean, lake=shutil.which('lake'), command=command,
    output=output/'edited-setups', label='manual', build_setups=setups)
files, excluded = compile_selected(prepared, patched, manifest['candidates'],
    project=ROOT, output=output, lean=lean, environment=dict(os.environ), threads=1, timeout=600)
report = dict(scope='exploratory manual complete-file compilation; no timing claim',
              accounting=accounting, files=files, excluded=excluded, setups=setup_records)
(output/'report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
print(output/'report.json')
