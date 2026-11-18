"""Weighted CM trace using the reviewed level-48 modular map and exact genus characters."""
import json,sys,random
from pathlib import Path
from math import gcd
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'heegner'))
from fast_trace import point_at,add,double,ctx,arb,acb

def represented_coprime(F,D):
    a,b,c=F
    for j in range(49):
        for i in range(49):
            m=a*i*i+b*i*j+c*j*j
            if gcd(i,j)==1 and m>0 and gcd(m,2*D)==1:return m
    raise ValueError("No primitive represented integer prime to 2D in box")

def weighted(d):
    ctx.prec=1024
    meta=json.loads((Path(__file__).resolve().parent.parent/'heegner'/('FAST-%d.json'%d)).read_text())
    assert d%17==0 and d%24==23
    hp=hm=0;P=[]
    for F in meta['forms']:
        assert F[1]**2-4*F[0]*F[2]==-d and F[0]%48==0 and F[1]%96==meta['orient']
        m=represented_coprime(F,d)
        q=pow(m,8,17)
        assert q in (1,16)
        x,y=point_at(d,F)
        if q==16:hm+=1;y=-y
        else:hp+=1
        P.append((x,y))
    assert hp==hm and hp+hm==meta['h']
    random.Random(2).shuffle(P)
    while len(P)>1:P=[add(P[j],P[j+1]) if j+1<len(P) else P[j] for j in range(0,len(P),2)]
    x,y=P[0]
    assert x.imag.contains(0) and y.imag.contains(0) and not y.real.contains(0)
    return dict(d=d,weighted_by=17,count_plus=hp,count_minus=hm,X=str(x),Y=str(y),sqrt_17_scaled_Y=str(y/arb(17).sqrt()))
if __name__=='__main__':print(json.dumps(weighted(int(sys.argv[1])),indent=2))
