#!/usr/bin/env python3
"""Read three frozen JSON inputs. Independently recompute all finite checks.

Only the standard library is used; none of the original elliptic, field,
chart, Gauss, ideal or weighted-trace implementation code is imported.
This checks the arithmetic on the submitted labels, not the classical
theorem identifying moduli specialization with the labeled isogeny paths.
"""
from collections import defaultdict
from hashlib import sha256
from itertools import product
from math import gcd, isqrt
from pathlib import Path
import json

P = 53
ROOT = Path(__file__).resolve().parents[2]
TRACE = ROOT / 'high-hom-1120/heegner-f53-descended'
CM = ROOT / 'joined-work-20261120/rc-d1-323-oriented-classes-r1'

def read(path, digest):
    data = path.read_bytes()
    assert sha256(data).hexdigest() == digest
    return json.loads(data)

def scalar(n):
    return (n % P, 0)

ZERO, ONE = scalar(0), scalar(1)

def add(a,b):
    return ((a[0]+b[0]) % P, (a[1]+b[1]) % P)

def neg(a):
    return ((-a[0]) % P, (-a[1]) % P)

def sub(a,b):
    return add(a,neg(b))

def mul(a,b):
    return ((a[0]*b[0]+22*a[1]*b[1]) % P, (a[0]*b[1]+a[1]*b[0]) % P)

def sq(a):
    return mul(a,a)

def divide(a,b):
    x,y=b
    inverse_denominator=pow((x*x-22*y*y)%P, -1, P)
    return mul(a,mul((x,-y),scalar(inverse_denominator)))

def cubic(x,n):
    return mul(mul(x,sub(x,scalar(n))),add(x,scalar(3*n)))

def group_add(a,b,n):
    if a is None:
        return b
    if b is None:
        return a
    x,y=a
    z,t=b
    if x == z:
        if add(y,t) == ZERO:
            return None
        slope=divide(sub(add(mul(scalar(3),sq(x)),mul(scalar(4*n),x)),scalar(3*n*n)),
                     mul(scalar(2),y))
    else:
        slope=divide(sub(t,y),sub(z,x))
    new_x=sub(sub(sq(slope),scalar(2*n)),add(x,z))
    return new_x, sub(mul(slope,sub(x,new_x)),y)

def multiply(k,a,n):
    if k<0:
        return multiply(-k,(a[0],neg(a[1])) if a else a,n)
    b=None
    while k:
        if k&1:
            b=group_add(b,a,n)
        a=group_add(a,a,n)
        k//=2
    return b

def from_json(a):
    return tuple(map(tuple,a)) if a is not None else None

def reduced_forms(discriminant):
    rows=[]
    for a in range(1,1+isqrt(-discriminant//3)):
        for b in range(-a,a+1):
            c,remainder=divmod(b*b-discriminant,4*a)
            if remainder or c<a or gcd(a,b,c)!=1 or ((abs(b)==a or a==c) and b<0):
                continue
            rows.append([a,b,c])
    return sorted(rows)

def all_chart_preimages(keys, field, roots):
    addresses=defaultdict(list)
    for x in field:
        if x==ZERO:
            continue
        x4=sq(sq(x))
        h=add(x4,ONE)
        for delta in roots[add(sq(h),mul(scalar(12),x4))]:
            y=divide(add(h,delta),scalar(2))
            if y==ZERO:
                continue
            T=add(sub(x,scalar(2)),divide(mul(scalar(3),x),y))
            U=sub(divide(sub(y,ONE),x),scalar(2))
            if (T,U) in keys:
                addresses[T,U].append((x,y))
    assert set(addresses)==set(keys)
    assert all(len(v)==1 for v in addresses.values())
    outputs={}
    for key,((x,y),) in addresses.items():
        r=divide(sub(x,divide(ONE,x)),scalar(2))
        s=divide(sub(sub(mul(scalar(2),y),sq(sq(x))),ONE),mul(scalar(4),sq(x)))
        assert sq(s)==add(add(sq(sq(r)),sq(r)),ONE)
        # Every actual key avoids the fiber of this exceptional r=0 chart.
        assert r != ZERO
        A=divide(add(s,ONE),sq(r))
        B=mul(sub(sq(A),ONE),r)
        raw=(add(mul(scalar(2),A),ONE),mul(scalar(2),B))
        assert sq(raw[1])==cubic(raw[0],-1)
        outputs[key]=group_add(raw,(scalar(3),ZERO),-1)
    return outputs

def gauss_sum(root, ell, lift_power, modulus):
    """Plain polynomial long remainder for the two independent fields."""
    n=len(modulus)-1
    def term(a):
        return tuple(a)+(0,)*(n-len(a))
    zero=term([])
    one=term([1])
    def pplus(a,b):
        return tuple((x+y)%P for x,y in zip(a,b))
    def ptimes(a,b):
        c=[0]*(2*n-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):
                c[i+j]+=x*y
        for i in range(len(c)-1,n-1,-1):
            x=c[i]%P
            for j in range(n):
                c[i-n+j]-=x*modulus[j]
        return tuple(x%P for x in c[:n])
    w=one
    z=term(root)
    for _ in range(lift_power):
        w=ptimes(w,z)
    assert w!=one
    squares={a*a%ell for a in range(1,ell)}
    total=zero
    z=one
    for a in range(1,ell):
        z=ptimes(z,w)
        total=pplus(total,z if a in squares else tuple(-x%P for x in z))
    assert ptimes(z,w)==one
    square_parameter=(ell if ell%4==1 else -ell)%P
    assert ptimes(total,total)==term([square_parameter])
    if ell==17:
        # k is embedded by u=8w^8.
        coeff=total[8]*pow(8,-1,P)%P
        u=term([0]*8+[8])
    else:
        # k is embedded by u=(w^9−25)/12.
        c=pow(12,-1,P)
        coeff=total[9]*12%P
        u=term([-25*c%P]+[0]*8+[c])
    constant=next(a for a in range(P) if
                  pplus(term([a]),tuple(coeff*x%P for x in u))==total)
    return constant,coeff

def main():
    detail=read(TRACE/'ACTUAL-FULL-TRACE-F53.json',
                '8d172729d64384eb192e718573a317e691f7f0862a291eacc4248aea22550a64')
    final=read(TRACE/'EXACT-FINAL-TRACE-F53.json',
               '8b47edaef8514e1ee554765cbdd4e10d03729b7a1ab889c8951fa3741e4c23d7')
    schedule=read(CM/'ORIENTED-CLASS-SCHEDULE-455.json',
                  'fbad2fa9c91ea586fda032f63331d448ec12d539fc687b6d140f070c016c1478')
    assert detail['schedule_sha']=='fbad2fa9c91ea586fda032f63331d448ec12d539fc687b6d140f070c016c1478'
    assert final['incoming_sha256']=='8d172729d64384eb192e718573a317e691f7f0862a291eacc4248aea22550a64'
    pts=detail['cases']
    assert [(c['relative_label'],c['relative_form']) for c in pts]==[
        (c['offset'],c['relative_form']) for c in schedule['relative_vertices']]
    assert len(pts)==20 and sorted(c['relative_form'] for c in pts)==reduced_forms(-455)
    slots=set(product(range(1,17),range(1,19)))
    squares17={a*a%17 for a in range(1,17)}
    squares19={a*a%19 for a in range(1,19)}
    emitted=defaultdict(set)
    total=None
    nrows=0
    for case in pts:
        i,j,k=case['relative_label']
        edges=case['horizontals']
        assert [e[2] for e in edges]==[29]*i+([7] if k else [])+([5] if j else [])
        source=[[0,0],[1,0]]
        for src,dst,_ in edges:
            assert src==source
            source=dst
        assert len(case['rows'])==len(slots)==288
        assert {(v['a17'],v['a19']) for v in case['rows']}==slots
        case_sum=None
        sum_of_signs=0
        for v in case['rows']:
            expected_sign=(1 if v['a17'] in squares17 else -1)*(1 if v['a19'] in squares19 else -1)
            assert v['w']==expected_sign
            sum_of_signs+=expected_sign
            point=from_json(v['phi'])
            assert point is None or sq(point[1])==cubic(point[0],-1)
            case_sum=group_add(case_sum,multiply(expected_sign,point,-1),-1)
            emitted[from_json(v['t16'])].add(point)
            nrows+=1
        assert sum_of_signs==0 and case_sum==from_json(case['weighted_raw_value'])
        total=group_add(total,case_sum,-1)
    assert nrows==detail['retained_signed_rows']==5760
    assert total==from_json(detail['raw_sum'])==from_json(final['sum_raw'])
    assert len(emitted)==416 and all(len(v)==1 for v in emitted.values())
    field=list(product(range(P),repeat=2))
    roots=defaultdict(list)
    for x in field:
        roots[sq(x)].append(x)
    chart_outputs=all_chart_preimages(emitted,field,roots)
    assert all(chart_outputs[key] in emitted[key] for key in emitted)
    card=1+sum(len(roots[cubic(x,323)]) for x in field)
    assert card==2912
    g17=gauss_sum(detail['common_phase17_field16'],17,19,[-2]+[0]*15+[1])
    g19=gauss_sum(detail['common_phase19_field18'],19,17,[1]+[0]*8+[-50]+[0]*8+[1])
    s=mul(g17,g19)
    assert g17==tuple(final['gauss17'])==(21,0)
    assert g19==tuple(final['gauss19'])==(0,4)
    assert s==tuple(final['gauss_minus323'])==(0,31) and sq(s)==scalar(-323)
    actual=(mul(sq(s),total[0]),mul(mul(sq(s),s),total[1]))
    detector=multiply(224,actual,323)
    assert actual==from_json(final['actual_E323_trace_residue'])==((1,0),(25,0))
    assert detector==from_json(final['actual_E323_prime13_detector'])==((42,0),(42,0))
    assert sq(actual[1])==cubic(actual[0],323) and multiply(13,detector,323) is None
    card5=1+sum((y*y-x*(x-323)*(x+3*323))%5==0 for x in range(5) for y in range(5))
    assert card5==4
    print(json.dumps({'checked_classes':len(pts),'checked_rows':nrows,'actual_chart_keys':len(emitted),
                      'sum_raw':total,'gauss_root':s,'trace_E323_F53':actual,
                      'order_13_projection_E323_F53':detector,'E323_F53_squared_card':card,
                      'E323_F5_card':card5},sort_keys=True,indent=2))

if __name__=='__main__':
    main()
