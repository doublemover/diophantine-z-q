from pathlib import Path
import json,collections,sys,hashlib,gzip
sys.set_int_max_str_digits(0)
p=Path(__file__).resolve().parent
d=p
C=149**16384

Q=json.loads((d/'QUADRICS.json').read_text()); z=collections.Counter()
for r in Q['rows']:
 ts=r['terms']
 shift=max(0,-min(t['parameterPower'] for t in ts))
 ps=[(t['monomial'],int(t['coefficient'])*C**(shift+t['parameterPower']))for t in ts]
 for m,a in ps:
  for n,b in ps:z[tuple(sorted(m+n))]+=a*b
z={k:int(x)for k,x in sorted(z.items()) if x};assert z[1,1,1,1]==1 and set(range(1,186))==set().union(*map(set,z))
# Self-contained fixed Z polynomial, no symbolic parameter. Hex stores literal integers losslessly.
raw=(json.dumps({'format':'explicit-integer-coefficients-signed-hex','variables':185,'freeInput':1,'degree':4,'terms':[[list(m),hex(v)]for m,v in z.items()]},separators=(',',':'))+'\n').encode()
(d/'FIXED-185.json.gz').write_bytes(gzip.compress(raw,mtime=0))
print(len(z),len(raw),len((d/'FIXED-185.json.gz').read_bytes()),max(abs(n).bit_length()for n in z.values()),hashlib.sha256(raw).hexdigest())
