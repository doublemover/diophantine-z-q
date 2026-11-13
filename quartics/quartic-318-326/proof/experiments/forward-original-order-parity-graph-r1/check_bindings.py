"""Hash/source diagnostics only, not mathematical acceptance."""
from pathlib import Path
import hashlib
import json
here = Path(__file__).resolve().parent
repo = here.parents[4]
application = json.loads((here/'APPLICATION.json').read_text())
for path, expected in application['source_bindings'].items():
    assert hashlib.sha256((repo/path).read_bytes()).hexdigest() == expected, path
manifest = json.loads((here/'SOURCE-MANIFEST.json').read_text())
for path, expected in manifest.items():
    assert hashlib.sha256((here/path).read_bytes()).hexdigest() == expected, path
print(json.dumps({'source_bindings_checked':len(application['source_bindings']),
                  'packet_files_checked':len(manifest), 'scope':'Exact-byte source binding only'}, indent=2))
