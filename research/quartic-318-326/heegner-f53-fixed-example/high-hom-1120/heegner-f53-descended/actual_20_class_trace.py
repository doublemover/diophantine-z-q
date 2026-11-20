#!/usr/bin/env python3
"""Complete exact oriented 20-class F53 trace, preserving one Weil phase.

The literal output can be zero. Nonzero requires the final sum, not one class.
"""
import argparse, hashlib, json, multiprocessing, sys
from pathlib import Path
from horizontal_fields import field
from one_class_weighted_trace import *

DP=Path(__file__).resolve().parent
SCHEDULE=DP.parent.parent/'joined-work-20261120/rc-d1-323-oriented-classes-r1/ORIENTED-CLASS-SCHEDULE-455.json'
SCHEDULE_DIGEST='fbad2fa9c91ea586fda032f63331d448ec12d539fc687b6d140f070c016c1478'
A0=[[0,0],[1,0]]

def install():
    install_fast_inverse(D8,[-2]+[0]*7+[1])
    install_fast_inverse(D16,[-2]+[0]*15+[1])
    install_fast_inverse(D18,[1]+[0]*8+[-50]+[0]*8+[1])

def marked(M,B,ell,r,act,seed):
    rng=Random(seed)
    n,m=(8,p**4-1) if M is D8 else (M.n,M.m)
    assert m%ell==0
    for _ in range(100):
        x=M.F.trim([rng.randrange(p) for _ in range(n)])
        y=M.sqrt(x**3+B.A*x+B.B)
        if y is None:continue
        T=B.mul(m//ell,(x,y))
        assert B.mul(ell,T) is None
        P=B.add(act(T),B.mul(r-1,T))
        if P is None:continue
        assert B.mul(ell,P) is None and act(P)==B.mul(r,P)
        return P
    raise AssertionError('no actual marked torsion')

def omega_after(edges,end):
    _,num,den=D16.descended_action(D16.E0,lambda P:map_point(D16,edges,P),E(D16,end))
    return Morphism(end,end,num,den,(1+D16.u)/2)

def horizontal():
    M12,M28=field(12,12),field(28,7)
    for M in [M12,M28]:install_fast_inverse(M,M.modulus)
    b=marked(D8,D8.E0,5,3,D8.omega,553)
    c=marked(M12,M12.E0,7,4,M12.omega,773)
    chain=[]
    R={}
    for i in range(5):
        A=A0 if not chain else chain[-1].dst
        b0=map_point(D8,chain,b)
        c0=map_point(M12,chain,c)
        bEdge=faster_odd_edge(D8,E(D8,A),b0,5)
        cEdge=faster_odd_edge(M12,E(M12,A),c0,7)
        bcEdge=faster_odd_edge(D8,E(D8,cEdge.dst),cEdge.at(D8)(b0),5)
        R[i,0,0]=list(chain)
        R[i,1,0]=chain+[bEdge]
        R[i,0,1]=chain+[cEdge]
        R[i,1,1]=chain+[cEdge,bcEdge]
        if i<4:
            action=M28.omega if i==0 else omega_after(chain,A).at(M28)
            h=marked(M28,E(M28,A),29,2,action,290+3*i)
            nextEdge=faster_odd_edge(M28,E(M28,A),h,29)
            chain=chain+[nextEdge]
    assert len(R)==20
    return R

def prepare(edges):
    A=A0 if not edges else edges[-1].dst
    G17=map_point(D16,edges,D16.generator(17,17))
    M17=faster_odd_edge(D16,E(D16,A),G17,17)
    G19=map_point(D18,edges+[M17],D18.generator(19,19))
    M19=faster_odd_edge(D18,E(D18,M17.dst),G19,19)
    chain=edges+[M17,M19]
    B=M19.dst
    omega=omega_after(chain,B)
    Q=tuple(mix(M,B,l,omega) for M,l in [(D16,17),(D18,19)])
    gs=tuple(map_point(D8,chain,D8.generator(n,l)) for n,l in [(16,2),(3,3)])
    return B,Q,gs

def align(A,P,Q,l,w):
    a=weil(A,P,Q,l)
    t=next(j for j in range(1,l) if a==w**j)
    Q=A.mul(pow(t,-1,l),Q)
    assert weil(A,P,Q,l)==w
    return Q,t

def run_class(meta,base,phase,charts):
    label,form,edges=meta
    B,((P17,Q17),(P19,Q19)),(g16,g3)=base if label==(0,0,0) else prepare(edges)
    B16,B18=[E(M,B) for M in (D16,D18)]
    w17,w19=[M.F(tuple(t)) for M,t in zip((D16,D18),phase)]
    Q17,t17=align(B16,P17,Q17,17,w17)
    Q19,t19=align(B18,P19,Q19,19,w19)
    Aout=D8.E(-D8.F.of(13)/3,-D8.F.of(70)/27)
    S=None;rows=[]
    for a in range(1,17):
        T17=faster_odd_edge(D16,B16,B16.add(B16.mul(a,P17),Q17),17)
        A18=E(D18,T17.dst)
        f=T17.at(D18); P19t,Q19t=f(P19),f(Q19)
        assert weil(A18,P19t,Q19t,19)==w19**17
        f=T17.at(D8); g16t,g3t=f(g16),f(g3)
        for b in range(1,19):
            T19=faster_odd_edge(D18,A18,A18.add(A18.mul(b,P19t),Q19t),19)
            f=T19.at(D8)
            point,key=low_value(E(D8,T19.dst),f(g16t),f(g3t),charts)
            w=leg(a,17)*leg(b,19)
            S=Aout.add(S,Aout.mul(w,short(point)))
            rows.append(dict(a17=a,a19=b,w=w,t16=dump_k(key),phi=dump_k(point)))
    if label==(0,0,0):assert dump_k(long(S))==[[24,44],[12,26]]
    return {'relative_label':label,'relative_form':form,'B':B,
            'prealign_pairing_exponents':[t17,t19],
            'horizontals':[[edge.src,edge.dst,len(edge.num)-1] for edge in edges],
            'weighted_raw_value':dump_k(long(S)),'rows':rows}

def worker(meta):
    ret=run_class(meta,BASE,PHASE,CHARTS)
    print('done',ret['relative_label'],ret['weighted_raw_value'],flush=True,file=sys.stderr)
    return ret

def main():
    opts=argparse.ArgumentParser()
    opts.add_argument('--jobs',type=int,default=4)
    opts.add_argument('--schedule',type=Path,default=SCHEDULE)
    arg=opts.parse_args()
    skey=hashlib.sha256(arg.schedule.read_bytes()).hexdigest()
    assert skey==SCHEDULE_DIGEST
    schedule=json.loads(arg.schedule.read_text())
    assert schedule['discriminant']==-455 and schedule['orientation_beta_mod_2N']==60875
    install()
    global BASE,PHASE,CHARTS
    H=horizontal()
    BASE=prepare([])
    B,((P17,Q17),(P19,Q19)),g=BASE
    PHASE=tuple(weil(E(M,B),P,Q,l).v for M,(P,Q),l in
                [(D16,(P17,Q17),17),(D18,(P19,Q19),19)])
    CHARTS=chart_cache()
    meta=[(tuple(v['offset']),v['relative_form'],H[tuple(v['offset'])])
          for v in schedule['relative_vertices']]
    assert len(set(r[0] for r in meta))==20
    with multiprocessing.get_context('fork').Pool(arg.jobs) as pool:
        cases=pool.map(worker,meta)
    Aout=D8.E(-D8.F.of(13)/3,-D8.F.of(70)/27)
    S=None
    for case in cases:
        P=case['weighted_raw_value']
        S=Aout.add(S,short(tuple(parse(D8,P)) if P else None))
    raw=long(S)
    if raw:assert raw[0]**p==raw[0] and raw[1]**p==-raw[1]
    s=next(i*D8.u for i in range(1,p) if -(323*D8.one)==(i*D8.u)**2)
    twist=lambda P: (-323*P[0],s**3*P[1]) if P else None
    actual=twist(raw)
    if actual:
        x,y=actual
        assert y*y==x*(x-323)*(x+3*323)
        assert x**p==x and y**p==y
    T13=twist(long(Aout.mul(224,S)))
    print(json.dumps(dict(schedule_sha=skey,field='F53[u]/(u²−22)',
          common_phase17_field16=PHASE[0],common_phase19_field18=PHASE[1],
          retained_signed_rows=sum(len(c['rows']) for c in cases),cases=cases,
          raw_sum=dump_k(raw),twist_s=dump_k((s,s))[0],
          twisted_trace_up_to_global_sign=dump_k(actual),
          order13_detector_twisted=dump_k(T13)),sort_keys=True,indent=2))

if __name__=='__main__':main()
