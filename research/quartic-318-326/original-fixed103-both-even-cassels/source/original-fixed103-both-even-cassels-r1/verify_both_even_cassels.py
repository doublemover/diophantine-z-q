#!/usr/bin/env python3
from itertools import product
import json

def parity(x): return x.bit_count()%2
def dot(A,x,y):
    return parity(sum((parity(a&y)<<i) for i,a in enumerate(A)) & x)
def inv(A):
    n=len(A); T=[a|1<<(n+i) for i,a in enumerate(A)]
    for i in range(n):
        j=next((j for j in range(i,n) if (T[j]>>i)&1),None)
        if j is None:return None
        T[i],T[j]=T[j],T[i]
        for j in range(n):
            if i!=j and (T[j]>>i)&1:T[j]^=T[i]
    return [a>>n for a in T]
def graph_matrix(v,q,j):
    return [a|((parity(a)^(((v^q^j)>>i)&1))<<i)
            for i,a in enumerate([10,5,2,1])]
def profiles(v,q,j):
    out={}
    for role,qv,jv in [('even_first',0,0),('odd_first',q,0),
                       ('even_second',0,j),('odd_second',q,j)]:
        A=graph_matrix(v,qv,jv); G=inv(A); assert G is not None
        out[role]=dict(block_rows=A,inverse_rows=G,
          effective_vv_vj_jj=[parity(v)^dot(G,v,v),dot(G,v,jv),parity(jv)^dot(G,jv,jv)],
          internal_coeff_v=[parity(a&v) for a in G],internal_coeff_j=[parity(a&jv) for a in G])
    return out
A=profiles(13,15,15); B=profiles(4,7,12)
assert [x['effective_vv_vj_jj'] for x in A.values()]==[[0,0,0]]*3+[[0,0,1]]
assert [x['effective_vv_vj_jj'] for x in B.values()]==[[0,0,0],[0,0,0],[1,1,1],[0,0,0]]
assert B['even_second']['internal_coeff_v']==[0,1,0,1]
assert B['even_second']['internal_coeff_j']==[1,0,1,0]
assert B['even_first']['internal_coeff_v']==[1]*4

# Local quadratic norm symbol (6,a)_2 under the exact normalized tangent.
dyadic=[(a,(-1)**((a-1)//2+(a*a-1)//8)) for a in (1,3,5,7)]
assert dyadic==[(1,1),(3,1),(5,-1),(7,-1)]
assert all(((-1)**((a-1)//2+(a*a-1)//8))*((-1)**(((5*a-1)//2)+(((5*a)**2-1)//8)))==-1 for a in (1,3,5,7))

# Completely arbitrary true (reciprocity-correct) directed miniature blocks.
def transpose(A):
    return [sum(((a>>j)&1)<<i for i,a in enumerate(A)) for j in range(len(A))]
def kernel(A):
    return {x for x in range(1<<len(A)) if all(not parity(a&x) for a in A)}
checks=0
for n in range(1,6):
    pairs=[(i,j) for i in range(n) for j in range(i+1,n)]
    for r in range(1<<n):
        if parity(r): continue
        for ups in product((0,1),repeat=len(pairs)):
            L=[0]*n
            for (i,j),l in zip(pairs,ups):
                L[i]^=l*((1<<j)|(1<<i))
                L[j]^=(l^(((r>>i)&1)*((r>>j)&1)))*((1<<i)|(1<<j))
            M=[a^((1<<i) if (r>>i)&1 else 0) for i,a in enumerate(L)]
            assert transpose(M)==[a^(r if (r>>i)&1 else 0) for i,a in enumerate(L)]
            assert kernel(transpose(M))==kernel(L)
            checks+=1

print(json.dumps(dict(four_node_internal=[10,5,2,1],
    odd_only={'attachments_v_q_j':[13,15,15],'table':A},
    even_bridge_only={'attachments_v_q_j':[4,7,12],'table':B},
    directed_small_truth_checks=checks, dyadic_class6=dyadic),indent=2))
