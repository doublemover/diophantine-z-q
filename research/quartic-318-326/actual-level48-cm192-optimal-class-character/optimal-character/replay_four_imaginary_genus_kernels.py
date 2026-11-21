#!/usr/bin/env python3
"""Recover both actual first-arm matrices and all four genus-annihilator kernels."""
import json

CORES={
    "+":[1921,128,292,512,48,20,1024,3,5,9,65],
    "-":[897,254,346,638,78,106,126,3,5,9],
}
out={}
for phase,c in CORES.items():
    n=len(c); q=n; p17=0; p3=n+1
    nbr=[{} for _ in range(n+2)]
    # lambda retained is e17. Thus recover ordinary deleted L0 by this flip.
    l0=c[:]; l0[0]^=1
    for p in range(n):
        for h in range(n):
            if p!=h:
                nbr[p][h]=(l0[p]>>h)&1
        nbr[p][q]=l0[p].bit_count()%2
        # all original p except q0 are 1 modulo 4
        nbr[q][p]=nbr[p][q]
        # (3/p), (p/3): only 17 amongst the non-q0 rows is nonsquare
        nbr[p][p3]=int(p==p17); nbr[p3][p]=int(p==p17)
    assert all(nbr[p][h]==nbr[h][p] for p in range(n+1) for h in range(n+1) if p!=h)
    # q0 is 7 mod 24: (3/q0)=-1 but (q0/3)=+1
    nbr[q][p3]=1; nbr[p3][q]=0
    results={}
    for tag,drop17,add3,want in (
        ("D",False,False,[0,127]), ("D/17",True,False,[0]),
        ("3D",False,True,[0]), ("3D/17",True,True,[0]),
    ):
        S=[p for p in range(n+1) if not (drop17 and p==p17)]
        if add3:
            S.append(p3)
        m=[]
        for p in S:
            row=0
            for h in S:
                if p==h:
                    b=(sum(nbr[p][r] for r in S if r!=p)%2) ^ int(p in (q,p3))
                else:
                    b=nbr[p][h]
                row|=b<<h
            m.append(row)
        M=sum(1<<p for p in S if p!=q)
        ker=[x for x in range(1<<(n+2)) if x&M==x and all((r&x).bit_count()%2==0 for r in m)]
        assert ker==want
        results[tag]={"rows":m, "row_indices":S, "column_mask":M, "kernel":ker}
    out[phase]={"published_sharp":c,"deleted_ordinary":l0,
                "q0_index":q,"3_index":p3,"four_fields":results}
# Four imaginary characters on C2^3: each is nontrivial on c=e0.
counts=[sum(((f&g).bit_count()%2)==0 for f in (1,3,5,7)) for g in range(8)]
assert counts==[4,0,2,2,2,2,2,2]
out["group_ring"]={"complex_conjugation":1,"four_imaginary_character_masks":[1,3,5,7],
                  "coefficients_before_conjugation_cancellation":counts}
print(json.dumps(out,sort_keys=True,indent=2))
