#!/usr/bin/env python3
"""Exact *unweighted* oriented direct CM4 residue for the bounded controls."""
from hashlib import sha256
from pathlib import Path
from collections import Counter,defaultdict
from math import gcd,isqrt
import sys,json,argparse
ROOT=Path(__file__).resolve().parent.parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--book',type=Path,default=ROOT/'odd2544-weight-primefree-r1'/'ACTUAL-ODD2544-MARKED-ORDERS-Q29.json')
parser.add_argument('--charts',type=Path,default=ROOT.parent.parent/'joined-work-20261120'/'rc-d1-f53-supersingular-low-map-r1'/'LOW-48-SUPERSINGULAR-F53.json')
parser.add_argument('--eisenstein',type=Path,default=ROOT/'paired-prime-surrogate-409-r1'/'eisenstein-replay-r1'/'eisenstein_representations.py')
parser.add_argument('--d',type=int,choices=(323,132107,1139,465851),default=323)
parser.add_argument('--compact',action='store_true',help='replace detailed chosen rows by their exact SHA')
args=parser.parse_args()
assert sha256(args.eisenstein.read_bytes()).hexdigest()=='d08e4d69aa8beaa7df50941a22032588fe58fb2c26b239f261b36978bf82e990'
assert args.eisenstein.name=='eisenstein_representations.py'
sys.path.insert(0,str(args.eisenstein.resolve().parent))
from eisenstein_representations import order_reps,cross,dot

PIN='aa650e289ef886c824cf93414845c9586c12e5db0d640f6a6d48452ca9bb1a8e'
BOOK=args.book
raw=BOOK.read_bytes()
assert sha256(raw).hexdigest()==PIN
book=json.loads(raw)
ps=53
CHART_PIN='421d8068d858eed68da492cb75d9d3b1e9bb3d2163eb10f3f762754504db1b3f'
CHART_BOOK=args.charts
charts=CHART_BOOK.read_bytes()
assert sha256(charts).hexdigest()==CHART_PIN
lookup={tuple(r['T']+r['U']):None if r['rows'][0]['phi'] is None else tuple(map(tuple,r['rows'][0]['phi']))
        for r in json.loads(charts)['records']}
assert len(lookup)==416
Z=(0,0); O=(1,0); W=((22,0),(0,15))
def add(x,y):return tuple((a+b)%ps for a,b in zip(x,y))
def sc(c,x):return tuple(c*a%ps for a in x)
def sub(x,y):return add(x,sc(-1,y))
def mul(x,y):return ((x[0]*y[0]+22*x[1]*y[1])%ps,(x[0]*y[1]+x[1]*y[0])%ps)
def div(x,y):
    u,v=y
    return sc(pow((u*u-22*v*v)%ps,-1,ps),mul(x,(u,-v)))
def frob(x):return (x[0],-x[1]%ps)
def neg(P):return None if P is None else (P[0],sc(-1,P[1]))
def ec(P,Q):
    if P is None or Q is None:return P or Q
    x,y=P; X,Y=Q
    if x==X:
        if Y==sc(-1,y):return None
        assert Y==y
        s=div(add(add(sc(3,mul(x,x)),sc(-4,x)),(-3,0)),sc(2,y))
    else:s=div(sub(Y,y),sub(X,x))
    z=sub(add(mul(s,s),(2,0)),add(x,X))
    return z,sub(mul(s,sub(x,z)),y)
def sm(c,P):
    z=None
    while c:
        if c&1:z=ec(z,P)
        c//=2
        P=ec(P,P)
    return z
assert sm(13,W) is None and W is not None
for P in lookup.values():
    if P:
        x,y=P
        assert mul(y,y)==mul(mul(x,add(x,O)),sub(x,(3,0)))
I=(1,0,0,1)
MM={q:[tuple(t for row in M for t in row) for M in book['exact_level_matrices'][str(q)]]
    for q in (16,3)}
def mat(n,a,v,e,shift):
    return tuple((pow(e,-1,n)*sum(u*A[i] for u,A in zip((a,*v),MM[n]))+shift*I[i])%n
                 for i in range(4))
def line(A,u,n,c):
    a,b,f,d=A
    x,y=u
    return ((a-c)*x+b*y)%n==0 and (f*x+(d-c)*y)%n==0
def classnum(D):
    assert D<0 and D%4 in (0,1)
    return sum(1 for a in range(1,isqrt(-D//3)+1)
               for b in range(-a,a+1)
               if (b*b-D)%(4*a)==0
               for c in ((b*b-D)//(4*a),)
               if a<=c and gcd(a,b,c)==1 and not (b<0 and (abs(b)==a or a==c)))

def finite_model_canonical_lines(u,v):
    A=(4*u%16,0,v%16,4*(u-v)%16)
    V=[(1,t) for t in range(16)]+[(t,1) for t in range(0,16,2)]
    assert len(V)==24
    d={c:[L for L in V if line(A,L,16,c)] for c in (0,4,8,12)}
    assert all(len(L)==1 and L[0][0]%4==0 and L[0][1]==1 for L in d.values())
    assert d[4*((u-v)%4)]==[(0,1)]
    return d

def crunch(d):
    assert d%24==11 and pow(-d%ps,26,ps)==ps-1
    assert all(d%(n*n) for n in range(2,isqrt(d)+1))
    D=16*d
    h=classnum(-d)
    assert classnum(-D)==6*h
    # Embedding omega0=(1+sqrt(-d))/2 as u+v*omega at2; v odd.
    uv=[(u,v) for u in range(4) for v in (1,3)
        if (2*u-v)%4==1 and (u*u-u*v+v*v)%4==(d+1)//4%4]
    assert len(uv)==2
    for u,v in uv:finite_model_canonical_lines(u,v)
    expected16=[4*((u-v)%4) for u,v in uv]
    expected3=[r for r in range(3) if (r*r-r+(d+1)//4)%3==0]
    assert expected3==[0,1]
    phase=next(r for r in range(1,ps) if (3*r*r-D)%ps==0)
    all_rows=defaultdict(list)
    all_prim_count=Counter()
    for cls in book['marked_classes']:
        H=cls['max_order_basis_columns']; e=cls['basis_denominator']
        K=[tuple(H[j][i] for j in range(1,4)) for i in range(1,4)]
        C=(cross(K[1],K[2]),cross(K[2],K[0]),cross(K[0],K[1]))
        dt=dot(K[0],C[0])
        marks=cls['exact_marks']
        j=tuple(cls['j'])
        for v in order_reps(H,e,D):
            dots=[dot(v,r) for r in C]
            assert all(z%dt==0 for z in dots)
            a=sum(H[0][i]*(dots[i-1]//dt) for i in range(1,4))
            b,c,g=v
            ntr=2*a-b-g
            assert ntr%e==0 and (ntr//e)%2==0
            tr=ntr//e
            phi=(3*b+2*c-g)*pow(3*e,-1,ps)%ps
            assert phi in (phase,ps-phase)
            U={n:mat(n,a,v,e,(4-tr)//2) for n in (16,3)}
            assert all((M[0]+M[3]-4)%q==0 and (M[0]*M[3]-M[1]*M[2]-4*(d+1))%q==0
                       for q,M in U.items())
            if not any(x%2 for x in U[16]):
                continue  # 2*omega0 already integral: source is not O4-optimal.
            all_prim_count[(phi,j)]+=1
            for z16 in (0,4,8,12):
                for z3 in expected3:
                    chosen=[r for r in marks
                         if line(U[16],r['inverse_transport_mark'][0],16,z16)
                         and line(U[3],r['inverse_transport_mark'][1],3,z3)]
                    assert len(chosen)==1 or (j==(0,0) and not chosen)
                    if chosen:
                        (r,)=chosen
                        all_rows[(phi,z16,z3)].append(dict(j=j,endomorphism_coordinates=[a,*v,e],
                              tr_before_shift=tr,alpha_matrix_16=U[16],alpha_matrix_3=U[3],
                              marks=r['inverse_transport_mark'],chart=r['t16_and_after3'],
                              projection_mod_13=r['lambda13_phi0']))
    assert len(all_rows)==16 and all(len(rr)==6*h for rr in all_rows.values())
    assert all(all_prim_count[(phase,j)]==all_prim_count[(ps-phase,j)]
               for j in map(lambda r:tuple(r['j']),book['marked_classes']))
    marks_of=lambda rr:Counter(tuple(r['chart']) for r in rr)
    j53=lambda k:(k[0],-k[1]%ps,k[2],-k[3]%ps)
    w3=lambda k:k[2:]+k[:2]
    assert all(marks_of(all_rows[(ps-phase,z16,z3)])==Counter({
                     j53(k):c for k,c in marks_of(all_rows[(phase,z16,z3)]).items()})
                     for z16 in (0,4,8,12) for z3 in expected3)
    assert all(marks_of(all_rows[(ph,z16,1)])==Counter({
                     w3(k):c for k,c in marks_of(all_rows[(ph,z16,0)]).items()})
                     for z16 in (0,4,8,12) for ph in (phase,ps-phase))
    assert all(sum(r['projection_mod_13'] for r in all_rows[(phase,z16,z3)])%13
          ==-sum(r['projection_mod_13'] for r in all_rows[(ps-phase,z16,z3)])%13
          for z16 in (0,4,8,12) for z3 in expected3)
    chosen=(phase,expected16[0],1)  # fixed moduli orientation, not inferred from nonzero.
    # The determinant δ/Nor(u) normalizer fixes the point, so these readings
    # count the relative ord-2 duplicates literally; 2 is a unit mod 13.
    full=sum(r['projection_mod_13'] for r in all_rows[chosen])%13
    sum0=None
    for r in all_rows[chosen]:
        P=lookup[tuple(r['chart'])]
        assert sm(224,P)==sm(r['projection_mod_13'],W)
        sum0=ec(sum0,P)
    assert sum0 and tuple(map(frob,sum0))==neg(sum0)
    assert sm(224,sum0)==sm(full,W) and full
    sqroot=(0,-phase*pow(36,-1,ps)%ps)
    assert mul(sqroot,sqroot)==(-d%ps,0)
    def twist(P):
        X,Y=P
        X=sc(-d,X)
        Y=mul(mul(mul(sqroot,sqroot),sqroot),Y)
        assert X[1]==Y[1]==0
        assert Y[0]**2%ps==X[0]*(X[0]-d)*(X[0]+3*d)%ps
        return X[0],Y[0]
    twist_sum=twist(sum0)
    twist_ring_projection=twist(sm(full,W))
    twist_hilbert_projection=twist(sm(full*pow(2,-1,13)%13,W))
    if d==323:
        assert sqroot==(0,22)
        assert twist_hilbert_projection==(42,11)
    rows=[dict(phase_sqrt_minus_16d_coefficient_relative_J=v[0],eigen16=v[1],
               eigen3=v[2],count=len(rr),distinct_charts=len({tuple(r['chart']) for r in rr}),
               signed_partition=dict(sorted(Counter(r['projection_mod_13'] for r in rr).items())),
               ring_trace_mod13=sum(r['projection_mod_13'] for r in rr)%13,
               maximal_Hilbert_trace_mod13=pow(2,-1,13)*sum(r['projection_mod_13'] for r in rr)%13)
          for v,rr in sorted(all_rows.items())]
    return dict(d=d,discriminant=-D,maximal_class_number=h,ring_class_number=6*h,
                actual_dyadic_models=uv,actual_candidate_eigen16=expected16,
                actual_chosen_local_orientation=chosen,
                chosen_ring_trace_mod13=full,chosen_maximal_Hilbert_trace_mod13=full*pow(2,-1,13)%13,
                finite_group_raw_ring_sum=sum0,finite_group_twist_root=sqroot,
                finite_group_raw_ring_sum_twisted=twist_sum,
                finite_group_ring_projection_twisted=twist_ring_projection,
                finite_group_hilbert_projection_twisted=twist_hilbert_projection,
                all_counter_frobenius_and_w3_conjugations_checked=True,
                all_local_type_orientation_checks=rows,
                all_exact_marks_of_chosen_trace=all_rows[chosen])
out=crunch(args.d)
if args.compact:
    rows=out.pop('all_exact_marks_of_chosen_trace')
    out['ordered_full_chosen_rows_sha256']=sha256(json.dumps(rows,separators=(',',':')).encode('ascii')).hexdigest()
print(json.dumps(out,indent=2))
