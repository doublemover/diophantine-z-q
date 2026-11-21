#!/usr/bin/env python3
"""Necessary two-coordinate comparison on the six prior scalar survivors."""
from pathlib import Path
from hashlib import sha256
from itertools import product
import json,sys
D=Path(__file__).resolve().parent
old=D.parent/'ct-fixed-b-scalar-prefilter-r1'
sys.path.insert(0,str(old))
import cheap_fixed_b_tangent_scalar_gate as A
F=A.F; B=A.B; t=A.t
src=old/'EXACT-SCALAR-GATE-JOINED-CANDIDATES.json'
assert sha256(src.read_bytes()).hexdigest()=='a0a242f5a7fbe660d94b720a84ad97fa90e88839ab8e65e24f193d93b5ca65f8'
us=[z['u'] for z in json.loads(src.read_bytes())['cases'] if z['status'].startswith('not excluded')]
assert us==[2749849,2891117,3262241,5685821,5791843,6162461]
def dot(a,b):return (a&b).bit_count()%2
def width(p):return 3 if p==2 else 2
def code(v,q,p):return A.loc(v,p)|(A.loc(q,p)<<width(p))
def local_kummer_pair(p,e):
    need=8 if p==2 else 4; out={0}
    for i,v in enumerate(e):
        rr=[v-a for a in e]
        rr[i]=A.prod(rr[j] for j in range(3) if j!=i)
        cs=[A.loc(q,p) for q in rr];assert cs[0]^cs[1]^cs[2]==0
        out.add(cs[0]|(cs[1]<<width(p)))
    for h in sorted(range(-12,13),key=abs):
      if len(out)==need:break
      for a in e:
        if len(out)==need:break
        for k in range(1,65):
          if k%p==0:continue
          X=a+k*A.powp(p,h);rr=[X-b for b in e]
          if not all(rr):continue
          cs=[A.loc(q,p) for q in rr]
          if cs[0]^cs[1]^cs[2]==0:out.add(cs[0]|(cs[1]<<width(p)))
          if len(out)==need:break
    return sorted(out) if len(out)==need else None
def local_alpha_pair(p,e,L):
    for h in sorted(range(-12,13),key=abs):
      for a in e:
        for k in range(1,65):
          if k%p==0:continue
          X=a+k*A.powp(p,h)
          rr=[(X-b)/c for b,c in zip(e,[B,1,B])]
          if not all(rr) or any(A.loc(q,p) for q in rr):continue
          R=[A.localroot(q,p,24) for q in rr]
          zz=[r[0] for r in R]+[F(1)]; N=[r[1] for r in R]
          v=[sum(c*z for c,z in zip(l,zz)) for l in L]
          error=[min(A.vp(c,p)[0]+n for c,n in zip(l,N) if c) for l in L]
          if all(q and r>=A.vp(q,p)[0]+(3 if p==2 else 1) for q,r in zip(v,error)):
            return code(v[1]*v[2],v[0]*v[2],p)
    return None

def accumulate(rows,n):
    piv={}
    for i,row in enumerate(rows):
        a,b=row[-2:]; I=1<<i
        while a:
            j=a.bit_length()-1
            if j not in piv:piv[j]=(a,b,I);break
            x,y,Z=piv[j];a^=x;b^=y;I^=Z
        else:
            if b:
                u=v=0
                for k,rr in enumerate(rows):
                    if I>>k&1:
                        x,y=rr[-2:];u^=x;v^=y
                assert (u,v)==(0,1)
                return None,I
    return piv,None
def solve_finite(piv,n):
    free=[i for i in range(n) if i not in piv]
    if len(free)>14:return None
    out=[]
    for x in range(1<<len(free)):
        v=sum((x>>k&1)<<i for k,i in enumerate(free))
        for i,(a,b,_) in sorted(piv.items()):
            if dot(v,a)!=b:v^=1<<i
        assert all(dot(v,a)==b for a,b,_ in piv.values())
        out.append(v)
    assert len(set(out))==len(out)==1<<len(free)
    return out
def build(u):
    la=F(16*u**4+24*u*u+1,32*u*u);Delta=la+t
    k=A.known[u]; assert la==F(*k['lambda_']) and Delta==F(*k['lambda_plus_t'])
    ff=[A.verify_factors(n,k[z]) for n,z in ((u,'u_factor'),(la.numerator,'lambda_factor'),
                                            (Delta.numerator,'lambda_plus_t_factor'))]
    S=sorted({2,2399,8912209,1185793321,*(p for f in ff for p in f)})
    C=[-1,*S]; n=len(C)
    co0=A.norm([F(1),-B,B*Delta]);co1=A.norm([F(B),-B,B*la]);co2=A.norm([F(B),-1,-B*t])
    p0=A.ternary_point(co0,S)
    p1=A.norm([1-la,1+la,F(2)])
    p2=[4619710060,B*41,2399*38613147]
    inds=[(1,2),(0,2),(0,1)]
    L=[]
    for (i,j),co,P in zip(inds,[co0,co1,co2],[p0,p1,p2]):
        assert sum(c*x*x for c,x in zip(co,P))==0
        r=[0,0,0,co[2]*P[2]];r[i]=co[0]*P[0];r[j]=co[1]*P[1];L.append(r)
    e=[F(0),B*t,-B*la];rows=[];skipped=[]
    for p in S:
        K=local_kummer_pair(p,e);off=local_alpha_pair(p,e,L)
        if K is None or off is None:
            skipped.append([p,K is None,off is None]);continue
        hs=[A.loc(g,p) for g in C];hs+= [a<<width(p) for a in hs]
        for u0 in range(1,1<<(2*width(p))):
            if any(dot(r,u0) for r in K):continue
            mask=sum(dot(r,u0)<<j for j,r in enumerate(hs))
            rows.append([p,u0,K,off,mask,dot(off,u0)])
    out=dict(u=u,support=C,rows=rows,skipped=skipped,tangent_coefficients=L)
    piv,contra=accumulate(rows,2*n)
    if piv is None:
        out.update(status='globally excluded, mixed affine inconsistency',input_mask=contra)
        return out
    vs=solve_finite(piv,2*n)
    if vs is None:
        out.update(status='unknown, bounded affine enumeration limit',rank=len(piv))
        return out
    out['prior_lift_count']=len(vs);out['global_variable_pivot_count']=len(piv); used=[]
    for p in A.cells_fast:
        W=F(A.cells[p]); f=(W*W-t)/B;k2=W*W+la
        if u%p==0 or p in S or not f or not k2 or A.loc(f,p) or A.loc(k2,p):continue
        if A.vp(f,p)[0] or A.vp(k2,p)[0]:continue
        root1=A.localroot(f,p,3)[0];root2=A.localroot(k2,p,3)[0]
        error=[2+min(A.vp(q,p)[0] for q in l[:3] if q) for l in L]
        branch=[]
        for sg,sh in product((1,-1),repeat=2):
            zz=[W,B*sg*root1,sh*root2,F(1)]
            v=[sum(c*z for c,z in zip(l,zz)) for l in L]
            if any(not q or A.vp(q,p)[0]>=r for q,r in zip(v,error)):break
            g0=v[1]*v[2];g1=v[0]*v[2]
            if A.vp(g0,p)[0]%2 or A.vp(g1,p)[0]%2:break
            branch.append(code(g0,g1,p))
        if len(branch)!=4:continue
        ell=sum(A.char(g,p)<<i for i,g in enumerate(C))
        test=lambda u0:dot(ell,u0)|(dot(ell<<n,u0)<<2)
        before=sorted({test(v) for v in vs})
        vs=[v for v in vs if test(v) in branch]
        used.append(dict(p=p,W_mod_p2=int(W),before=before,ball=sorted(set(branch)),
                         aggregate_functional_mask=(ell^(ell<<n)),
                         remaining=len(vs)))
        if not vs:break
    out.update(status=('excluded by retained cells via two coordinates' if not vs else
                     'not excluded by this necessary test only'),
               remaining_lift_masks=vs,applied_contact_rows=used)
    if u==2749849:
        # Much shorter certificate than enumerating all retained cells.
        P=[r for r in used if r['p'] in (3162001,17590513)]
        assert len(P)==2 and all(q['ball']==[0,5] for q in P)
        B2=rows+[[r['p'],r['aggregate_functional_mask'],0] for r in P]
        C2,I=accumulate(B2,2*n);assert C2 is None and I
        out['two_cell_xor_certificate']=dict(
            appended_contact_rows=B2[-2:],original_local_row_count=len(rows),
            nonzero_input_indices=[i for i in range(len(B2)) if I>>i&1],
            contradiction=[0,1])
    return out

print(json.dumps(dict(source_sha256=sha256(src.read_bytes()).hexdigest(),
       cases=[build(u) for u in us],pocklington_certificates=A.primality,
       scope='literal six prior scalar survivors, no stated rank, global point, or actual source pole'),
       sort_keys=True,indent=2))
