#!/usr/bin/env python3
"""Finite degree-five Hecke operator on the exact 13/19 oriented level chart."""
import importlib.util, json, hashlib
from collections import Counter
from pathlib import Path
from functools import lru_cache

BASE=Path(__file__).resolve().parent.parent
DONORS={
    13:("ct-level48-inert13-complete-oriented-toy-pilot-r1",
        "replay_inert13_complete_pilot.py"),
    19:("ct-level48-inert19-complete-pilots-and-actual-three-part-r1",
        "replay_inert19_complete_pilot.py"),
}
PIN={
    13:"f6d1bbf36b6b82874f1b24cabb76f1425f130ca6021c80edba51661d3631990c",
    19:"6d15bdf5570395cd25c7d9fde0670bd9f3ec29e926b36de241b3a06494e07ff0",
}
LOOK="EXACT-INERT13-19-ORDERED-LOOKUP.json"
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def module(root, name, l):
    path=root/name
    list_hashes={x.split()[1]:x.split()[0] for x in (root/"SHA256SUMS").read_text().splitlines()}
    assert list_hashes[name]==digest(path)==PIN[l]
    spec=importlib.util.spec_from_file_location(f"t{l}",path)
    s=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(s)
    return s

def rank(rows):
    rows=[list(map(lambda x:x%3,r)) for r in rows]
    if not rows:return 0, []
    n=len(rows[0]); dims=0; pivots=[]
    for i in range(n):
        t=next((j for j in range(dims,len(rows)) if rows[j][i]),None)
        if t is None:continue
        rows[dims],rows[t]=rows[t],rows[dims]
        if rows[dims][i]==2:rows[dims]=[(2*z)%3 for z in rows[dims]]
        for j in range(len(rows)):
            if j!=dims and rows[j][i]:
                t=rows[j][i];rows[j]=[(x-t*y)%3 for x,y in zip(rows[j],rows[dims])]
        dims+=1;pivots.append(i)
    return dims,pivots

def one(l):
    root=BASE/DONORS[l][0]
    s=module(root,DONORS[l][1],l)
    assert digest(root/LOOK)=="6c941b5ae921d5a38741bf9c1770e1483ac06e021164b03a03c3cc461c9325cc"
    chart_raw=json.loads((root/LOOK).read_text())[str(l)]
    def code(g):return g[0]+l*g[1]
    def dec(i):return i%l,i//l
    chart={tuple(map(dec,k)):tuple(v) for k,v in chart_raw}
    assert len(chart)==(96 if l==13 else 144)==len(set(chart.values()))
    pts=sorted(chart.values()); idx={q:i for i,q in enumerate(pts)}
    swap_3={v:chart[k[1],k[0]] for k,v in chart.items()}
    adj={}
    def w3(q): return swap_3[q]
    def fc(q):
        x,y=map(dec,q)
        return tuple(map(code,(s.pw(x,l),s.pw(y,l))))
    def w48(q):
        x,y=map(dec,q);x1=s.s(x,s.z(1))
        return tuple(map(code,(s.d(s.a(x,s.z(1)),x1),
                              s.d(s.m(s.z(4),y),s.pw(x1,4)))))
    def hyper(q):
        x,y=map(dec,q)
        return code(x),code(s.n(y))
    def nx(q):
        x,y=map(dec,q)
        return code(s.n(x)),code(y)
    phases={}
    for q in pts:
        P=s.phi(*map(dec,q))
        v=s.etm(4,s.eadd(P,s.ng(s.pi(P)))) if l==19 else s.mu(4,s.eadd(P,s.ng(s.pi(P))),s.c(-3),s.c(-2))
        phases[q]=v
    G=next(v for v in phases.values() if v is not None)
    assert set(phases.values())=={None,G,s.ng(G)}
    for i in pts:
        phases[i]=0 if phases[i] is None else 1 if phases[i]==G else -1
        assert fc(i) in idx and w48(i) in idx and hyper(i) in idx and nx(i) in idx
    for i in pts:
        assert phases[fc(i)]==phases[w48(i)]==phases[w3(i)]==phases[hyper(i)]==phases[nx(i)]==-phases[i]
    charts_by_model={}; forget16={}; rows3=set()
    for A,B in ((10,7),) if l==13 else ((-1,5),(-1,0)):
        s.L0,s.B0=s.c(A),s.c(B)
        assert (s.q-1)%5==0 and (l**4-1)%5==0
        G16,G3,G5=(s.reps(2,4),s.reps(3,1),s.reps(5,1))
        assert (len(G16),len(G3),len(G5))==(24,4,6)
        t16=lru_cache(maxsize=None)(s.t16)
        def labels(A,B,U,V):
            t=t16(U,A,B)
            A3,B3,f3=s.velu(A,B,[V,s.ng(V)])
            return chart[t,t16(f3(U),A3,B3)]
        kernels=[]
        for Q in G5:
            K=[s.mu(i,Q,s.L0) for i in range(1,5)]
            assert None not in K and len(set(K))==4 and s.mu(5,Q,s.L0) is None
            A5,B5,f=s.velu(s.L0,s.B0,K)
            kernels.append((A5,B5,[f(Q) for Q in G16],[f(Q) for Q in G3]))
        charts_by_model[f"{A},{B}"]=0
        xy={(j,k):labels(s.L0,s.B0,U,V) for j,U in enumerate(G16) for k,V in enumerate(G3)}
        for j,U in enumerate(G16):
            row=tuple(sorted(xy[j,k] for k in range(4)))
            assert len(set(row))==4 and sum(phases[x] for x in row)%3==0
            rows3.add(row)
            C8=s.mu(2,U,s.L0)
            matching=[i for i,W in enumerate(G16)
                      if s.mu(2,W,s.L0) in [s.mu(t,C8,s.L0) for t in (1,3,5,7)]]
            assert len(matching)==2 and j in matching
            j2=next(i for i in matching if i!=j)
            for k in range(4):
                x,y=xy[j,k],xy[j2,k]
                assert x!=y and phases[x]+phases[y]==0
                if x in forget16:assert forget16[x]==y
                forget16[x]=y
        for j,U in enumerate(G16):
            for k,V in enumerate(G3):
                x=xy[j,k]
                if x not in adj:charts_by_model[f"{A},{B}"]+=1
                neigh=sorted(labels(A5,B5,U5[j],V5[k]) for A5,B5,U5,V5 in kernels)
                if x in adj:assert adj[x]==neigh
                adj[x]=neigh
    assert set(pts)==set(adj)==set(forget16)
    assert all(forget16[forget16[x]]==x for x in pts)
    assert len(rows3)*4==len(pts)
    ct={q:Counter(adj[q]) for q in pts}
    for x in pts:
        assert sum(phases[y] for y in adj[x])%3==phases[x]%3
        for y in pts:assert ct[x][y]==ct[y][x]
        assert sorted(fc(y) for y in adj[x])==adj[fc(x)]
        assert sorted(w48(y) for y in adj[x])==adj[w48(x)]
        assert sorted(w3(y) for y in adj[x])==adj[w3(x)]
    def signed(*operators):
        blocks={}; zeros=set(); assign={}
        for x in pts:
            if x in assign or x in zeros:continue
            orbit={}
            conflict=False
            for j in range(2**len(operators)):
                y,sgn=x,1
                for k,op in enumerate(operators):
                    if (j>>k)&1:y,sgn=op(y),-sgn
                if y in orbit and orbit[y]!=sgn:conflict=True
                orbit[y]=sgn
            if conflict:
                zeros.update(orbit)
            else:
                for y,sgn in orbit.items():assign[y]=(x,sgn)
                blocks[x]=orbit
        heads=sorted(blocks);hidx={x:i for i,x in enumerate(heads)}
        assert len(zeros)+len(assign)==len(pts)
        A5=[]
        for x in heads:
            line=[0]*len(heads)
            for y in adj[x]:
                if y in assign:
                    h,sgn=assign[y];line[hidx[h]]+=sgn
            A5.append(line)
        dims,piv=rank([[x-(i==j) for j,x in enumerate(row)] for i,row in enumerate(A5)])
        return {"signed_dim":len(heads),"T5_eigenvalue_1_dim":len(heads)-dims,"pivots":piv}
    for x in pts:
        assert fc(w3(x))==w3(fc(x)) and w48(w3(x))==w3(w48(x)) and fc(w48(x))==w48(fc(x))
    T5=[[ct[x][y]-(x==y) for y in pts] for x in pts]
    def joint_constraints(shifts, hecke=False, trace3=False):
        rows=[]
        for op in shifts:
            rows.extend([[(x==y)+(op(x)==y) for y in pts] for x in pts])
        if trace3: rows.extend([[y in a for y in pts] for a in sorted(rows3)])
        if hecke: rows.extend(T5)
        r,pv=rank(rows)
        return len(pts)-r
    return {
        "prime":l, "charts_from_each_source":charts_by_model,
        "finite_T5_identity":True, "phase_target_generator":G,
        "hec_a5":-2, "negative_Frob_w48":signed(fc,w48),
        "negative_Frob_w48_w3":signed(fc,w48,w3),
        "plus_negative_hyper_and_X_neg_samespace_dimension":joint_constraints([fc,w48,w3,hyper,nx]),
        "plus_negative_hyper_and_X_neg_T5_eigenvalue_1_dim":joint_constraints([fc,w48,w3,hyper,nx],True),
        "true_forget16_and_3_neutral_then_T5_dim":joint_constraints([fc,w48,w3,forget16.__getitem__],True,True),
        "plus_all_normalizers_and_true_traces_T5_dim":joint_constraints([fc,w48,w3,hyper,nx,forget16.__getitem__],True,True),
        "direct_six_neighbor_phase_all_true":True,
        "forget16_bijective_fixed_free":True,
        "total_3line_neutral_fibers":len(rows3),
        "T5_commutes_with_hyper":all(sorted(hyper(y) for y in adj[x])==adj[hyper(x)] for x in pts),
        "T5_commutes_with_X_neg":all(sorted(nx(y) for y in adj[x])==adj[nx(x)] for x in pts),
        "full_chart": [[list(x),phases[x], list(map(list,adj[x]))] for x in pts],
    }

if __name__=="__main__":
    print(json.dumps({l:one(l) for l in (13,19)},indent=2,sort_keys=True))
