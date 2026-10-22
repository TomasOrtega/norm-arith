"""Pack and verify the retained exploratory records before removing duplicates."""
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

HERE = Path(__file__).resolve().parent
receipt = json.loads((HERE/'receipt.json').read_bytes())
archive = HERE/'trial-evidence.tar.gz'
sha = lambda data: hashlib.sha256(data).hexdigest()
with archive.open('xb') as stream, gzip.GzipFile(fileobj=stream, mode='wb', mtime=0, filename='') as compressed:
    with tarfile.open(fileobj=compressed, mode='w|') as tar:
        for name, entry in sorted(receipt['retained_files'].items()):
            data = (HERE/name).read_bytes()
            assert len(data) == entry['bytes'] and sha(data) == entry['sha256']
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = len(data), 0o644, 0
            tar.addfile(info, io.BytesIO(data))
seen = {}
with tarfile.open(archive, 'r:gz') as tar:
    for member in tar:
        assert member.isfile() and member.name not in seen
        data = tar.extractfile(member).read()
        seen[member.name] = {'sha256': sha(data), 'bytes': len(data)}
assert seen == receipt['retained_files']
record = {'schema_version': 1, 'status': 'roundtrip_verified',
    'archive': archive.name, 'archive_sha256': sha(archive.read_bytes()), 'archive_bytes': archive.stat().st_size,
    'members': len(seen), 'uncompressed_bytes': sum(row['bytes'] for row in seen.values()),
    'member_index': 'receipt.json:retained_files', 'member_index_file_sha256': sha((HERE/'receipt.json').read_bytes()),
    'scope': 'Exact reports, all successful and failed trial logs, copied sources, actual header setups and setup command logs; original .lake trial directories remain intact.'}
with (HERE/'transport.json').open('x') as stream:
    stream.write(json.dumps(record, indent=2)+'\n')
shutil.rmtree(HERE/'trial-evidence')
print(json.dumps(record))
