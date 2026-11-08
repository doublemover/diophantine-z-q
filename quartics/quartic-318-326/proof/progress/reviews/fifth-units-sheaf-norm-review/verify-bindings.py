from pathlib import Path
import hashlib,json,sys
base=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/workspace/scratch/2cb21e4e0864')
data=json.loads((Path(__file__).parent/'BINDINGS.json').read_text())
for path,expected in data['files'].items():
    actual=hashlib.sha256((base/path).read_bytes()).hexdigest()
    assert actual==expected,(path,expected,actual)
print('ALL_BOUND_FILES_PASS',len(data['files']))
