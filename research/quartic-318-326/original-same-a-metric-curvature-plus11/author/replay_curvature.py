"""Exact integer/rational replay. No floating point, remote input or Lean."""
from fractions import Fraction as Q
from itertools import combinations
from math import prod
import json

b=(0,32,-343,76832)
w=(560,560,80,7)
D=560
c=960
cut=10**6
k=64
a22=4*2765952000**2//25725
assert a22*25725==4*2765952000**2
P=420*2765952000**2//a22
assert P*a22==420*2765952000**2
alpha=Q(1957,720)
assert alpha==sum(1/Q(prod(range(1,n+1))) for n in range(7))

# Independent exact replay of the seven ranges from the heartbeat.
dr=[
 (c*16*243*76000,2*2220**3),
 (c*68*143*76000,2*2440**3),
 (Q(c)*200*168*76000/7,2*2870**3),
 (c*368*57*76000,2*3500**3),
 (Q(c)*Q(19,20)*Q(1,2)*Q(68832,8000),2*Q(51,10)**3),
 (Q(c)*Q(99,100)*Q(95,100)/4,2*Q(241,100)**3),
 (Q(76832)**2*Q(99,100)*Q(95,100)/(80*102443),2*Q(241,100)**3),
]
seven=[Q(n,d) for n,d in dr]
assert min(seven)>7 and min(seven)==Q(175104000,23639903)
assert Q(P,7)==385875<alpha**13
assert alpha**13*720**13-385875*720**13==783383856877292891662687036024772111640757

def section(x,y):
    assert 0<=x<y<=cut
    low=[max(0,x-abs(t),abs(t)-y) for t in b]
    upper=c*D+sum(wi*(y+abs(t)) for wi,t in zip(w,b))
    first=c*D*sum(w[i]*prod(low[j] for j in range(4) if i!=j) for i in range(4))
    second=sum(w[i]*w[j]*(b[i]-b[j])**2*
               prod(low[l] for l in range(4) if l not in (i,j))
               for i,j in combinations(range(4),2))
    return (D*(first+second),2*upper**3)

todo=[(0,cut)]
rows=[]
while todo:
    x,y=todo.pop()
    n,d=section(x,y)
    if n>=k*d:
        rows.append((x,y,n,d))
    else:
        assert y-x>=2
        m=(x+y)//2
        todo.extend(((m,y),(x,m)))
assert len(rows)==44
assert rows[0][0]==0 and rows[-1][1]==cut
assert all(a[1]==b[0] for a,b in zip(rows,rows[1:]))
lowest=min(rows,key=lambda r:Q(r[2],r[3]))
# For every r>=cut: r_j/r>=9/10 and U/r<=11/5.
assert 1-Q(max(map(abs,b)),cut)>=Q(9,10)
assert Q(sum(w),D)+Q(c*D+sum(wi*abs(t) for wi,t in zip(w,b)),D*cut)<=Q(11,5)
tail=Q(c*sum(w),D)*Q(9,10)**3/(2*Q(11,5)**3)
assert tail>k
assert Q(P,k)<alpha**11
assert 64*1957**11-P*720**11>0
print(json.dumps({
  'contacts':b,'weight_numerators':w,'common_weight_denominator':D,
  'unchanged_metric_constant':c,'checked_original_7_range_values':[str(x) for x in seven],
  'same_finite_divisor':a22,'raw_arch_constant_after_finite_divisor':P,
  'unchanged_metric_lower_bound':k,'tail_cut':cut,'tail_curvature_lower':str(tail),
  'finite_rows':rows,'weakest_finite_interval':lowest[:2],
  'weakest_finite_lower':str(Q(lowest[2],lowest[3])),
  'arch_ratio_bound':str(Q(P,k)),'strict_exp_11_integer_margin':64*1957**11-P*720**11
},indent=2,sort_keys=True))
