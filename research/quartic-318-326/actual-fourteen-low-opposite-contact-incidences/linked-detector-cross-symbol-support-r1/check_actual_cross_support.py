#!/usr/bin/env python3
"""Exact cross-leg squareclass constraints using only archived literal prime records."""
from hashlib import sha256
from math import prod
from pathlib import Path
import json
root=Path(__file__).resolve().parent.parent
def get(rel,h):
    b=(root/rel).read_bytes()
    assert sha256(b).hexdigest()==h
    return json.loads(b)
tri=get('linked-detector-three-scale-incidence-r1/EXACT-THREE-SCALE-INCIDENCE.json',
        'a6a7cd4966b0fdb11ba00b17fa2a7422347f13963a0be1d331a3ff448169cfec')
six=get('linked-detector-six-compatible-incidences-r1/EXACT-SIX-INCIDENCES.json',
        'd8884f7363646097c1a5d260f11ebad2475bbe37ecae5a2124c60aec5481e1b0')
assert tri['literal_scalar_J']==six['literal_scalar_J']
assert int(six['prior_triad_h_residue'])==int(tri['simultaneous_h_residue'])
assert int(six['prior_triad_h_modulus'])==int(tri['simultaneous_h_modulus'])
roots={1:(-1,2),2:(-1,1),3:(1,2399),4:(-32,407)}
classes=[(k,i) for k in range(3) for i in roots]
def sign(x,p):
    u=pow(x%p,(p-1)//2,p)
    assert u in (1,p-1)
    return 1 if u==1 else -1
def case(rows,old_obstruction_primes):
    taken={(k,i):[z['prime'] for z in rows if i==2 and k==z['assigned_scale']] for k,i in classes}
    assert len(set(p for a in taken.values() for p in a))==len(rows)
    values=[]; witnesses={}
    for z in rows:
        p=z['prime']; hit=(z['assigned_scale'],2); p2=p*p
        A=z['r_over_d_mod_p2']; C=z['scales_mod_p2']
        assert A%p and all(c%p for c in C)
        k0=[a*pow(b,-1,p)*pow(c*c,-1,p)%p for c in C for a,b in roots.values()]
        assert k0==z['distinct_nonzero_scaled_roots_mod_p'] and len(set(k0))==12 and 0 not in k0
        out=[]
        for k,i in classes:
            a,b=roots[i]
            F=(C[k]**2*A**2-a*pow(b,-1,p2))%p2
            if (k,i)==hit:
                assert F==p
                F//=p
            else:
                assert F%p
            known=prod(q for q in taken[k,i] if q!=p)
            raw=sign(F,p)
            out.append([k,i,F,raw,raw*sign(known,p)])
            if i!=2 and raw==-1:
                witnesses.setdefault((k,i),p)
        values.append({'prime':p,'hit':hit,'rows':out})
    assert len(witnesses)==9
    for j,l in enumerate(old_obstruction_primes):
        assert sign(prod(taken[j,2]),l)==-1
    return {'known_incidences':len(rows), 'same_class_still_forced_by_small_primes':old_obstruction_primes,
            'forced_unhit_classes':[[k,i,witnesses[k,i]] for k,i in sorted(witnesses)],
            'total_support_lower_bound':len(rows)+3+len(witnesses),'local_symbol_rows':values}
print(json.dumps({'root_indices':roots, 'class_order':classes,
  'row_layout':['scale','root index','exact factor unit mod p² unless hit (then factor quotient by p mod p)','actual unit sign','remaining unknown squareclass sign'],
  'triad':case(tri['rows'],[7,7,7]),
  'six':case(tri['rows']+six['rows'],[23,19,19])},indent=2))
