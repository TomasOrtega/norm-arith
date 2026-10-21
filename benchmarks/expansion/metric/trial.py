"""Compile whole-file metric prototype proposals without registering a Lake module."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'scripts'))
from benchmark import prepare_sources
from verify_selection import compile_selected

parser = argparse.ArgumentParser()
parser.add_argument('--manifest', type=Path, default=Path(__file__).with_name('manifest.json'))
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--prototype', type=Path, default=ROOT/'.lake/metric-expansion-prototype-v2')
parser.add_argument('--path', action='append')
args = parser.parse_args()
output, prototype = args.output.resolve(), args.prototype.resolve()
if output.exists():
    raise SystemExit('output must be new')
output.mkdir(parents=True)
manifest = json.loads(args.manifest.read_text())
if args.path:
    chosen = set(args.path)
    manifest['files'] = [row for row in manifest['files'] if row['path'] in chosen]
    manifest['candidates'] = [row for row in manifest['candidates'] if row['path'] in chosen]
(output/'input-manifest.json').write_text(json.dumps(manifest, ensure_ascii=False, indent=2)+'\n')
prepared, accounting = prepare_sources(manifest, ROOT/'.lake/packages/mathlib')
setups = {}
for row in prepared:
    path = output/'sources'/row['path']
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(row['replacement'])
    module = row['path'][:-5].replace('/', '.')
    setup_path = ROOT/'.lake/census-full-v3/setups'/f'{module}.json.gz'
    setup = json.loads(gzip.decompress(setup_path.read_bytes()))
    setup['importArts']['MetricPrototype'] = [
        [str(prototype/('MetricPrototype'+suffix)) for suffix in ['.olean','.olean.server','.olean.private']],
        [str(prototype/('MetricPrototype'+suffix)) for suffix in ['.ir.sig','.ir']]]
    setups[row['path']] = setup
    target = output/'input-setups'/f'{module}.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(setup, ensure_ascii=False, indent=2)+'\n')
environment = dict(os.environ)
environment['LEAN_PATH'] = str(prototype)+os.pathsep+environment.get('LEAN_PATH','')
files, excluded = compile_selected(prepared, setups, manifest['candidates'], project=ROOT,
    output=output, lean=shutil.which('lean'), environment=environment, threads=1, timeout=600)
report = dict(scope='Exploratory scratch metric extension; no production or timing claim',
    accounting=accounting, files=files, excluded=excluded,
    prototype={str(path): hashlib.sha256(path.read_bytes()).hexdigest()
               for path in sorted(prototype.glob('MetricPrototype.*')) if path.is_file()},
    setup_policy='Original census build setup/options plus explicit prototype artifact and LEAN_PATH fallback')
(output/'report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
print(output/'report.json')
