#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
P=Path(__file__).resolve().parent.parent/'ct-original-scalar-kummer-fiber-r1'
pins=json.loads((P/'PINNED-SCALAR-FIBER.json').read_text())
expected=(P/'EXACT-ACTUAL-SCALAR-LAMBDA.json').read_bytes()
assert hashlib.sha256(expected).hexdigest()=='f4ed8565184d24655508774f3278e5585e9a140bc4038f71fac87c9980d94ab6'
assert subprocess.check_output([sys.executable,'-B',str(P/'verify_actual_scalar_lambda.py')])==expected
S=json.loads(expected)
R=pins['R_input']; beta=S['beta']; D0=1+114444*R; G=432*beta
def val(n,p):
 assert n
 e=0
 while n%p==0:n//=p;e+=1
 return e
rows=[]
for m in S['places']:
 p=m['p']; N=m['N'] # a p-adic-integral lift, sufficient for every unit check
 a,b,c=G*R**2,2*G*R*N**2,D0**2+G*N**4
 I,J=b*b+12*a*c,72*a*b*c-2*b**3
 assert b*b-4*a*c==-4*a*D0**2
 assert 4*I**3-J**2==432*a*c*(b*b-4*a*c)**2
 assert I%p==16*G**2*R**2*N**4%p!=0
 assert val(a,p)==val(c,p)==val(I,p)==0 and val(D0,p)==1
 e=val(16*I**3,p)-val(a*c*(b*b-4*a*c)**2,p)
 assert e==-4
 rows.append(dict(p=p,N_mod_p=N,R_mod_p=R%p,G_mod_p=G%p,I_mod_p=I%p,
   a_mod_p=a%p,c_mod_p=c%p,D0_valuation=val(D0,p),jC_valuation=e,
   jTarget_valuation=val(2048,p)-val(3,p)))
assert S['places'][0]['annihilator']==324*101
assert S['places'][0]['h_residue']==18*324
assert S['places'][0]['chart_h']!=[0,0]
assert S['places'][1]['annihilator']%101!=0
base=[(s,i,j) for s in ['zero/pole','pole/zero'] for i in range(4) for j in range(4)]
assert len(set(base))==32
print(json.dumps(dict(source_h=S['h'],beta=beta,normalizer_checks=rows,
 labeled_base_points=base,both_source_j=1728,target_j='2048/3',
 orbit_101_check=[S['places'][0]['annihilator'],S['places'][0]['h_residue'],
 S['places'][1]['annihilator']%101],
 koszul_h0=2*16-1+2,surface_h1_anti=(2*16-1+2)-32,
 scope='full-chart generic fixed-fiber no-section, no actual specialization claim'),indent=2,sort_keys=True))
