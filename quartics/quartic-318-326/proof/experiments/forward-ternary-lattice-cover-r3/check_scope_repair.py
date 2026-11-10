#!/usr/bin/env python3
from pathlib import Path
import json,re
H=Path(__file__).resolve().parent;O=H.parent/'forward-ternary-lattice-cover-r2'
i=json.loads((O/'intake.json').read_text());changed=[]
for n in i['order']:
 if (H/(n+'.lean')).read_bytes()!=(O/(n+'.lean')).read_bytes():changed.append(n)
assert changed==['SquarefreeTernaryLatticeCover318']
s=(H/'SquarefreeTernaryLatticeCover318.lean').read_text()
assert re.sub(r'^include (?:hp hd|hd|hp) in\n','',s,flags=re.M)==(O/'SquarefreeTernaryLatticeCover318.lean').read_text()
assert len(re.findall(r'^include ',s,re.M))==6
assert not re.search(r'/--(?:(?!-/).)*-/\ninclude ',s,re.S)
print(json.dumps({'unchanged_sources':265,'targeted_includes':6,'lean_run':False},indent=2))
