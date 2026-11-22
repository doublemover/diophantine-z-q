#!/usr/bin/env python3
from hashlib import sha256
from math import prod
from pathlib import Path
import json

old=Path(__file__).resolve().parent.parent / "original-a0-h328-t18-known-nine-pure-second-r1" / "PINNED-OLD-T18-REPLAY.json"
raw=old.read_bytes()
assert sha256(raw).hexdigest()=="7c94388b54349fe6247aa8baace6cbba3f94db8f3c6e2f8e4717308d5cf96d0f"
data=json.loads(raw)
n,beta=data["squarefree_amplitude"],data["beta"]
table=data["screens"]["first"]["table"]
columns=[-1]+[p for p,_,_ in table]
assert len(columns)==18 and columns[:3]==[-1,2,3] and prod(columns[3:])==n
assert n%24==17 and beta>1 and n%beta==0

def code(a,p):
    v=0
    while a%p==0:
        a//=p
        v^=1
    if p==2:
        return v|{1:0,3:6,5:4,7:2}[a%8]
    ch=pow(a%p,(p-1)//2,p)
    assert ch in (1,p-1)
    return v|(2 if ch==p-1 else 0)

def mask_of(d):
    out=0
    if d<0:
        d=-d
        out=1
    for i,p in enumerate(columns[1:],1):
        if d%p==0:
            d//=p
            out|=1<<i
    assert d==1
    return out

def reduce_insert(w,pivots):
    while w and w.bit_length()-1 in pivots:
        w^=pivots[w.bit_length()-1]
    if w:
        pivots[w.bit_length()-1]=w
    return w

rows,pivots=[],{}
for p,img,_ in table:
    dim=3 if p==2 else 2
    x_image=sorted(set(x% (1<<dim) for x in img))
    annihilator=[t for t in range(1,1<<dim)
                       if all((t&w).bit_count()%2==0 for w in x_image)]
    for t in annihilator:
        row=sum(((t&code(q,p)).bit_count()%2)<<j for j,q in enumerate(columns))
        r=reduce_insert(row,pivots)
        rows.append([p,x_image,row,r])
assert len(pivots)==9
rational=[mask_of(q) for q in (beta,-3,n)]
rp={}
for w in rational:
    assert all((row[2]&w).bit_count()%2==0 for row in rows)
    assert reduce_insert(w,rp)
print(json.dumps({"signed_columns":columns,"projected_rows_and_pivots":rows,
                  "fixed_dual_selmer_dimension":len(columns)-len(pivots),
                  "rational_x_basis":[beta,-3,n],
                  "rational_x_image_dimension":len(rp),
                  "sha_fixed_isogenous_2_primary_dimension":len(columns)-len(pivots)-len(rp),
                  "scope":"fixed G0/Q only, not the moving twist, its relative kernel or h328 bare bit"},indent=2))
