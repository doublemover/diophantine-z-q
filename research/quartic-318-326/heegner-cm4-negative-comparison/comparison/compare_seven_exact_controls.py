#!/usr/bin/env python3
"""Check old weighted coefficients against exact direct-CM4 residues."""
from hashlib import sha256
from pathlib import Path
import json,subprocess,sys
T=Path(__file__).resolve().parent
B=T.parent
def read(path,pin):
    b=(B/path).read_bytes()
    assert sha256(b).hexdigest()==pin
    return json.loads(b)
r19=read('paired-prime-surrogate-409-r1/EXACT-TORIC-PAIR-Q19.json',
         '682d536ec5f7bbfead58b9369e0d3d8a70b8282b63f0ebe490d6a53ae0f0401b')
r67=read('paired-prime-surrogate-409-r1/EXACT-TORIC-PAIR-Q67.json',
         '94057f0c94ff781d9dda1ad7f548257f265d2dc23c5a84c7c2d9b086a12700ee')
short=read('odd2544-bounded-negative-probe-r1/SHORT-AUXILIARIES-CALIBRATION.json',
           '7862e774c0adfbecd60c57fb305ff2a024eee68f021eb25c84300372ff6bb388')
match=read('odd2544-bounded-negative-probe-r1/SHORT-MATCHED-LOCAL-COUNTERCONTROL.json',
           '32cfbd34e2b0e10fdd9e07fb4cf0601256516f47f8d3fdce94be4f7b9534a68b')
v={-r['D']:r for r in [*r19,*r67,short['first_negative_aux_seed'],*(s['negative'] for s in match['rows'])]
   if r['D']<0}
out=[]
for d in sorted(v):
    r=v[d]
    assert r['aux_l']==37 and sum(r['raw_mod13_representatives_by_class'])%13==r['coefficient_mod13']
    direct=json.loads(subprocess.check_output([sys.executable,'-B',str(T/'check_extended_direct.py'),'--d',str(d),'--compact']))
    a=r['coefficient_mod13']
    h=direct['chosen_maximal_Hilbert_trace_mod13']
    assert h*h%13==4*a*a%13
    out.append(dict(d=d,negative_A37=a,direct_Hilbert=h,square_mod13=h*h%13,
                    direct_ring_rows=direct['ring_class_number'],
                    raw_direct_on_Eminus1=direct['finite_group_raw_ring_sum'],
                    marked_rows_sha256=direct['ordered_full_chosen_rows_sha256']))
assert len(out)==7
print(json.dumps(out,indent=2))
