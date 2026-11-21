import itertools
D=10
def test(p):
    Z=(0,)*D
    def c(x):return (x%p,)+(0,)*(D-1)
    def add(a,b):return tuple((x+y)%p for x,y in zip(a,b))
    def neg(a):return tuple(-x%p for x in a)
    def sub(a,b):return add(a,neg(b))
    def mul(a,b):return tuple(sum(a[j]*b[k-j] for j in range(k+1))%p for k in range(D))
    def inv(a):
        u=pow(a[0],-1,p)
        b=[u]
        for k in range(1,D):b.append(-u*sum(a[j]*b[k-j] for j in range(1,k+1))%p)
        b=tuple(b)
        assert mul(a,b)==c(1)
        return b
    def pow_(a,n):
        v=c(1)
        for _ in range(n):v=mul(v,a)
        return v
    def poly(a,x):
        v=Z
        for b in a[::-1]:v=add(mul(v,x),c(b))
        return v
    t=(0,1)+(0,)*(D-2)
    normal=station=quot=0
    for a,b in itertools.product(range(p),repeat=2):
        if (b*b-a*a*a+a)%p:continue
        for q,scale in itertools.product(range(p),[1,2]):
            s=mul(pow_(t,scale),add(c(1),mul(c(q),t)))
            w=Z
            for _ in range(D):w=sub(pow_(s,3),mul(s,pow_(w,2)))
            assert add(w,mul(s,pow_(w,2)))==pow_(s,3)
            A,B=c(a),c(b)
            u=inv(add(c(1),mul(s,w)))
            beta=inv(sub(c(1),mul(A,mul(pow_(s,2),u))))
            H=sub(add(mul(c(2),B),mul(sub(mul(c(3),pow_(A,2)),c(1)),s)),
                  mul(add(pow_(A,3),A),w))
            x=add(A,mul(mul(mul(s,u),pow_(beta,2)),H))
            assert x[:2]==(a, (2*b*(scale==1))%p)
            # Compare to the cleared actual stock slope, without dividing
            # t−Aw in a truncated ring (it is *not* a unit).
            d=sub(s,mul(A,w))
            num=sub(mul(w,pow_(add(c(1),mul(B,w)),2)),
                    mul(add(s,mul(c(2*a),w)),pow_(d,2)))
            assert num==mul(sub(x,A),mul(w,pow_(d,2)))
            if scale==1:normal+=1
            else:station+=1
            for Bcoef in [(1,1,1),(1,2,3),(2,1,0)]:
                if poly(Bcoef,c(a))[0]==0:continue
                for Acoef in [(1,2,3),(3,0,1),(1,1,0)]:
                    Q=mul(poly(Acoef,x),inv(poly(Bcoef,x)))
                    aa=poly(Acoef,c(a))[0]; bb=poly(Bcoef,c(a))[0]
                    da=(Acoef[1]+2*a*Acoef[2])%p; db=(Bcoef[1]+2*a*Bcoef[2])%p
                    assert Q[:2]==(aa*pow(bb,-1,p)%p,(da*bb-aa*db)*pow(bb,-2,p)*x[1]%p)
                    quot+=1
    return normal,station,quot
totals=tuple(map(sum,zip(*(test(p) for p in (5,7,11,13)))))
print('actual cleared mixed chord regular arc:',totals[0])
print('actual cleared mixed chord stationary arc:',totals[1])
print('same-arc integral rational first jets:',totals[2])
