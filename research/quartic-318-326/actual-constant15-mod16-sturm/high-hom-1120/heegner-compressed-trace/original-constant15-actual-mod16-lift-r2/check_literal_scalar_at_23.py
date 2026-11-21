"""Integer certificates for the formal-branch reduction and level data."""
import json

p=23
h=473592745039516333133760
J=15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000
beta=204618888056724185
R=4376874610839020
K=1+114444*R

def leg(a,q):
    z=pow(a%q,(q-1)//2,q)
    return z if z<=1 else -1

arms=[]
for r in (5,18):
    assert r*r%p==2
    D=(3-r)**2%p; x,y=(1+r)%p,2*r%p
    assert D and (y*y-(x*x-D)*x)%p==0
    num=1+sum(1+leg(z*(z*z-D),p) for z in range(p))
    assert num==24
    arms.append([r,D,num])

def ind(N,primes):
    for q in primes:
        assert N%q==0
        N=N//q*(q+1)
    return N

def redforms(delta):
    from math import gcd,isqrt
    out=[]
    for a in range(1,isqrt(-delta//3)+1):
        for b in range(-a,a+1):
            if (b*b-delta)%(4*a):continue
            c=(b*b-delta)//(4*a)
            if a>c or gcd(gcd(a,b),c)>1:continue
            if (a==abs(b) or a==c) and b<0:continue
            out.append([a,b,c])
    return out

i_mod24=pow(6,15,24)*pow(3,65536,24)*J%24
i_mod23=pow(6,15,p)*pow(3,65536,p)*J%p
m=i_mod23*pow(h,-1,p)%p
assert h%24==i_mod24==0 and i_mod23 and h%p
W=(1+pow(m,4,p)*pow(R,-29,p))%p
c0=12*W*pow(K,-1,p)%p
delta=(1-beta*c0*c0)%p
assert c0==1 and delta==7 and beta*delta%p==4
assert leg(beta,23)==leg(4840,23)==-1
assert leg(-15,11)==-1 and leg(-30,11)==leg(-30,23)==1
assert leg(30,17)==1
levels=[(29040,[2,3,5,11]),(15840,[2,3,5,11]),(174240,[2,3,5,11])]
indices=[ind(n,qs) for n,qs in levels]
forms=redforms(-120)
assert forms==[[1,0,30],[2,0,15],[3,0,10],[5,0,6]]
print(json.dumps(dict(arms=arms,h_mod23=h%p,i_mod23=i_mod23,m=m,R=R%p,K=K%p,W=W,c0=c0,delta=delta,beta_delta=beta*delta%p,shift=4840%p,disc_minus120_forms=forms,levels=[n for n,_ in levels],indices=indices,sturm=[x//6 for x in indices]),sort_keys=True,indent=2))
