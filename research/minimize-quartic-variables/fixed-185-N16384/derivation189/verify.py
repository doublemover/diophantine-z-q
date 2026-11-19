import gzip,json,collections,time,pathlib,hashlib,math
p=pathlib.Path(__file__).resolve().parent
r=json.loads((p/'QUADRICS.json').read_text())['rows']
d=collections.defaultdict(int);C=149**16384
for row in r:
 ts=row['terms'];mn=min(t['parameterPower'] for t in ts); shift=max(0,-mn)
 for i,t in enumerate(ts):
  for j in range(i+1):
   s=ts[j];a=int(t['coefficient'])*int(s['coefficient'])*(1 if i==j else 2)*pow(C,2*shift+t['parameterPower']+s['parameterPower'])
   d[tuple(sorted(s['monomial']+t['monomial']))]+=a
raw=gzip.decompress((p/'FIXED-189.json.gz').read_bytes()); f=json.loads(raw); k={tuple(m):int(h,16) for m,h in f['terms']};assert k=={m:v for m,v in d.items() if v};print(len(k),len(set(i for m in k for i in m)),max(map(len,k)),max(abs(i).bit_length() for i in k.values()),k[(1,)*4],hashlib.sha256(raw).hexdigest())
m=json.loads((p/'WITNESS-MANIFEST.json').read_text()); assert hashlib.sha256(raw).hexdigest()==m['fixedUncompressedSha'] and len(k)==m['terms'] and len(set(v for t in k for v in t))==m['coordinates'] and max(map(len,k))==4 and max(abs(i).bit_length() for i in k.values())==m['maxAbsCoefficientBits'] and k[(1,)*4]==1
