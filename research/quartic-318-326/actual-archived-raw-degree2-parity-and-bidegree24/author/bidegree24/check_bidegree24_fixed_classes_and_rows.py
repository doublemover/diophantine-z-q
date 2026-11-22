from hashlib import sha256
from pathlib import Path
import json
H=Path(__file__).resolve().parents[2]/'high-hom-1120/heegner-compressed-trace'
def read(p,h):
 data=p.read_bytes();assert sha256(data).hexdigest()==h
 return json.loads(data)
shadow=read(H/'original-a0-factorless-companion-norm-line-r1/PINNED-SCALAR-FIBER.json',
            'e26e3478e3980e48a762cde5eb9755f0e22c31db1b41e748f7b117ec15b2aefb')
sh=H/'original-linear-q-a0-exact-anchor-depth-full-scalar-r1'
m=(sh/'SHA256SUMS').read_bytes()
assert sha256(m).hexdigest()=='9dc74e33f8afb1fdb40aae98ed766ab5bedb8f8cb63b828c4bc04f401e9b34f5'
pins=dict(reversed(line.split(maxsplit=1)) for line in m.decode().splitlines())
p='EXACT-A0-FULL-SCALAR-ANCHOR-DEPTH.json'
sharp=read(sh/p,pins[p])
h=int(shadow['h']);i=6**15*3**65536*int(shadow['J'])
def val(n,p):
 v=0;assert n
 while n%p==0:n//=p;v+=1
 return v
assert h%20==i%20==0
assert (val(h,17),val(i,17))==(1,2)
# Unit formal coefficient at both split places from the exact donor.
u=sharp['chartU20_mod_289']
assert u==[34,272] and list(map(lambda a:val(a,17),u))==[1,1]
vn=[2*(1+val(j,17)) for j in (h,i)]
assert vn==[4,6]
R=4376874610839020
assert val(R,17)==0 and val(114444*R,17)==2
beta=204618888056724185
assert val(beta,17)==1 and 17*114444*R==204**2*beta
# Norm-depth proof gives v17(b)=2 and thus δ square unit, unlike β.
# Finite rational coefficients in the four explicit double-root checks:
# write each other form as const*(a*(λ² X)^2 + b*δ*(λ² X)Y+c*δ²Y²).
rows=[('beta','P',(1,-10,9)),('beta','Q',(1,14,1)),
      ('minus3beta','Q',(3,10,3)),('minus3beta','P',(-1,14,-1))]
# In final row the natural normalized coefficient is δ/3, declared below.
out=[]
for fibre,squared,(a,b,c) in rows:
 d=b*b-4*a*c
 assert d in (64,192)
 out.append([fibre,squared,[a,b,c],d])
print(json.dumps(dict(archived_index_depths17=[val(h,17),val(i,17)],
                      chartU20_mod289=u,known_norm_depths17=vn,
                      known_B_class_depth17=val(beta,17),
                      fibre_rows_other_polynomial=out,
                      final_row_delta_scale='1/3'),indent=2,sort_keys=True))
