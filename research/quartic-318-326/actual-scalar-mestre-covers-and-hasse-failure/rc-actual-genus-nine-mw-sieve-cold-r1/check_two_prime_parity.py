

A,B=-2,65
P=(5,20); T=(0,0)
beta=204618888056724185
def add(P,Q,p):
    if P is None:return Q
    if Q is None:return P
    x,y=P;u,v=Q
    if x==u:
        if (y+v)%p==0:return None
        m=(3*x*x+2*A*x+B)*pow(2*y,-1,p)%p
    else:m=(v-y)*pow(u-x,-1,p)%p
    w=(m*m-A-x-u)%p
    return w,(m*(x-w)-y)%p
for p,order in ((17,8),(131,14)):
    v=(P[0]%p,P[1]%p);lst=[None]
    while (g:=add(lst[-1],v,p)) is not None:lst.append(g)
    assert len(lst)==order
    if p==17:assert T not in lst and lst[2][0]==1 and lst[-2][0]==1
    print(p,lst)
for p,c in ((3,6),(11,10)):
    num=1+sum((y*y-x*(x*x+A*x+B))%p==0 for x in range(p) for y in range(p))
    assert num==c
    print(p,num)
assert beta%17==0 and beta%289!=0 and pow((-3)%17,8,17)==16
assert beta%131==27 and 27 in {x*x%131 for x in range(1,131)} and (-3)%131 not in {x*x%131 for x in range(1,131)}
# primitive quartics bad mod 8 after dividing respective powers of 2
sq8={x*x%8 for x in range(8)}
for d in (2,-2):
    for m in (1,2,4,8):
        for e in range(1,8,2):
            r=d*m**4+4*m*m*e*e+(-256//d)*e**4
            k=1 if m%2 else 16 if m%4 else 64
            assert r%k==0 and r//k%8 not in sq8
print('exact independent small control PASS')
