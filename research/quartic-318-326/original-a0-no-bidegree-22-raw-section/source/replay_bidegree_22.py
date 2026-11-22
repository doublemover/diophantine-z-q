import json
from itertools import permutations
from math import gcd

points=((0,1),(1,0))
def cross(m):
    a,b,c=m; return (
       a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0]))
def eq(v,w):
    x,y=v; s,t=w
    return x*t==s*y
def img(M,v):
    a,b,c,d=M; x,y=v
    return a*x+b*y,c*x+d*y
def row(v,w):
    x,y=v; s,t=w
    return t*x,t*y,-s*x,-s*y
def interpolate(vw):
    rows=[row(v,w) for v,w in vw]
    M=[(-1)**i*cross([r[:i]+r[i+1:] for r in rows]) for i in range(4)]
    g=gcd(*M)
    assert g>0
    M=[q//g for q in M]
    if (M[3] or M[2])<0: M=[-q for q in M]
    a,b,c,d=M
    assert a*d-b*c and all(eq(img(M,v),w) for v,w in vw)
    return M
out=[]
for roots in permutations(((1,1),(-3,1))):
    for v in points:
        for w in points:
            M=interpolate([((1,1),roots[0]),((-3,1),roots[1]),(v,w)])
            stays=sum(any(eq(img(M,u),u2) for u2 in points) for u in points)
            assert stays in (1,2)
            a,b,c,d=M
            K=(a-c)*(a+3*c)
            assert (a-c)*(b+3*d)+(b-d)*(a+3*c)==2*K
            assert (b-d)*(b+3*d)==-3*K
            out.append(dict(input=v,image=w,root_permutation=roots,M=M,K=K,retained=stays==1))
good=[(tuple(x["M"]),x["K"]) for x in out if x["retained"]]
assert set(good)=={((-2,3,1,0),-3),((0,3,1,2),-3),((-3,0,-2,3),9),((-1,-2,0,1),1)}
print(json.dumps(out,indent=2,sort_keys=True))
