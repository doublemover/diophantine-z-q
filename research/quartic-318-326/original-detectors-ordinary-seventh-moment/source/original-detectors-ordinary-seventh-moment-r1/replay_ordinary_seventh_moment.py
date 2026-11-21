#!/usr/bin/env python3
from math import gcd,isqrt
from functools import reduce
from operator import xor
import json
from weber_seventh_moment import consume, leading_jet, powers

def divpoly(a,b):
    n=b.bit_length()
    c=0
    while a and a.bit_length()>=n:
        k=a.bit_length()-n
        c^=1<<k
        a^=b<<k
    assert not a
    return c

def cube_inflate(a):
    return sum((a>>i&1)<<(3*i) for i in range(a.bit_length()))


def reduced_forms(D):
    return [(a,b,(b*b-D)//(4*a)) for a in range(1,isqrt(abs(D)//3)+1)
        for b in range(-a,a+1) if (b*b-D)%(4*a)==0 and
        a<=(b*b-D)//(4*a) and (b>=0 or (abs(b)!=a and a!=(b*b-D)//(4*a)))
        and gcd(gcd(a,b),(b*b-D)//(4*a))==1]

def prime(p):
    return p>=2 and all(p%i for i in range(2,isqrt(p)+1))

class GF:
    def __init__(self,f,mod):
        self.f=f
        self.N=1<<f
        self.M=self.N-1
        assert mod>>f==1
        L=[-1]*self.N; P=[]; a=1
        for i in range(self.M):
            assert L[a]==-1 and a>0
            L[a]=i;P.append(a)
            a<<=1
            if a&self.N:a^=mod
        assert a==1 and L[0]==-1
        self.L=L;self.P=P
        self.trace_mask=sum(self.rawtrace(1<<i)<<i for i in range(f))
    def pow(self,a,k):
        return self.P[(self.L[a]*k)%self.M] if a else int(k==0)
    def mul(self,a,b):
        return self.P[(self.L[a]+self.L[b])%self.M] if a and b else 0
    def trace(self,a):
        return (a & self.trace_mask).bit_count()&1
    def rawtrace(self,a):
        s=0
        for i in range(self.f):
            s^=a;a=self.pow(a,2)
        assert s in (0,1)
        return s
    def wht(self):
        A=[0]+[1-2*self.trace(self.pow(a,-1)) for a in range(1,self.N)]
        for j in range(self.f):
            k=1<<j
            for i in range(0,self.N,2*k):
                for h in range(i,i+k):
                    x,y=A[h],A[h+k]
                    A[h],A[h+k]=x+y,x-y
        return A
    def trace_dual(self,a):
        return sum(self.trace(self.mul(a,1<<i))<<i for i in range(self.f))
    def neighbors(self,a):
        b=self.pow(a,pow(3,-1,self.M))
        t=self.pow(b,8)
        assert self.trace(t)==0
        y=0
        for i in range((self.f+1)//2):
            y^=t
            t=self.pow(t,16)
        assert self.pow(y,4)^y==self.pow(b,8)
        ans=[self.mul(b,y),self.mul(b,y^1)]
        assert all(x>0 and self.pow(x,4)^self.mul(a,x)^self.pow(a,4)==0 for x in ans)
        return ans
    def components(self,A):
        S=set(A);unseen=set(A);out=[]
        while unseen:
            a=min(unseen);C={a};todo=[a]
            while todo:
                a=todo.pop()
                for b in [self.pow(a,2)]+self.neighbors(a):
                    assert b in S
                    if b not in C:
                        C.add(b);todo.append(b)
            assert C<=unseen
            unseen-=C;out.append(C)
        return out
    def orbit(self,a):
        C=[a]; b=self.pow(a,2)
        while b!=a:
            C.append(b);b=self.pow(b,2)
        return C
    def factor(self,C):
        out=[1]
        for a in C:
            nxt=[0]+out
            for i,v in enumerate(out):
                nxt[i]^=self.mul(a,v)
            out=nxt
        assert set(out)<={0,1}
        return sum(v<<i for i,v in enumerate(out))
    def jet(self,C):
        h=[1]+[0]*7
        for a in C:
            for i in range(7,0,-1):
                h[i]^=self.mul(a,h[i-1])
        assert set(h)<={0,1}
        return h

def control(d,q,f,mod,t):
    D=-17*d*q
    if d>1:
        assert prime(d) and d%24==1 and pow(q,(d-1)//2,d)==1
    assert prime(q) and q%24==7 and pow(q,8,17)==16
    assert t%4==1 and t*t-4*(1<<f)==D and t%3==0 and f%2==1
    assert D%24==1
    K=GF(f,mod); W=K.wht()
    roots=[a for a in range(1,K.N) if W[K.trace_dual(a)]==-t]
    F=reduced_forms(D)
    assert len(roots)==len(F)
    out=[]
    for S in K.components(roots):
        assert len(S)==len(roots)//(2 if d>1 else 1)
        R=set(S);polys=[];PHI=0;bad=0;BOTH=0;Jets=[]
        assert len(S)%f==0 and (len(S)//f)%2==0
        while R:
            a=min(R);C=K.orbit(a)
            assert len(C)==f and set(C)<=R
            R-=set(C)
            B=[K.pow(b,pow(3,-1,K.M)) for b in C]
            direct=K.trace(K.pow(B[0],7));j=K.jet(B)
            assert direct==powers(j)[6]
            assert powers(j)[0]==0 and powers(j)[2]==((1+(1<<f)-t)//4)%2
            PHI^=direct
            p=K.factor(B);r=K.factor(C)
            assert j==leading_jet(p)
            Jets.append(j)
            inflate=cube_inflate(r)
            other=divpoly(inflate,p)
            assert other.bit_length()-1==2*f
            bad^=powers(leading_jet(inflate))[6]
            TWO=powers(leading_jet(other))[6]
            BOTH^=TWO
            assert TWO==direct and powers(leading_jet(inflate))[6]==0
            polys.append([a,r,p,other,direct])
        actual_edges={(min(a,b),max(a,b)) for a in S for b in K.neighbors(a)}
        assert len(actual_edges)==len(S) and all(a!=b for a,b in actual_edges)
        edge=reduce(xor,(K.pow(a^b,5) for a,b in actual_edges),0)
        data=consume(Jets)
        assert edge==PHI==BOTH==data["phase"]==data["simplified_phase"] and bad==0
        out.append({"least_reciprocal_j":min(S),"degree":len(S),
          "frobenius_rows":[{"least_reciprocal_j":a,"reciprocal_j_irred_bits":p,
             "reciprocal_gamma2_irred_bits":g,"other_pair_irred_bits":other,
             "seventh_trace":v} for a,p,g,other,v in polys],
          "reciprocal_gamma2_top_jet":data["jet"],"power_sums_1_to_7":data["power_sums"],
          "unoriented_horizontal_edge_phase":edge,"all_three_cube_branches_phase":bad,
          "other_two_cube_branches_phase":BOTH})
    return {"D":D,"d":d,"qstar":q,"f":f,"modulus_bits":mod,"Frob_trace_t":t,
            "h":len(F),"components":out}

if __name__=='__main__':
    def M(*e): return sum(1<<i for i in e)
    print(json.dumps([control(1,7,5,M(5,2,0),-3),
      control(193,7,13,M(13,4,3,1,0),-99)],indent=2))
