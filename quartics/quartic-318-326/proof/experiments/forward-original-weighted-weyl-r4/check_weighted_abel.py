#!/usr/bin/env python3
"""Exact finite Abel/line phase tests, plus explicitly numerical chord sanity checks."""
from pathlib import Path
import json,math

def Q(k,x):return x[0]**2+x[1]**2-x[2]**2-x[3]**2-k*x[4]**2
def B(k,h,v):return h[0]*v[0]+h[1]*v[1]-h[2]*v[2]-h[3]*v[3]-k*h[4]*v[4]
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def line(y,v,j):return tuple(a+j*b for a,b in zip(y,v))
def W(x):return 1+sum((i+1)*z*z-(i+2)*z for i,z in enumerate(x))
def phase(q,n,a=1):
    out=[0]*q;out[n%q]=a;return out
def padd(a,b):return [x+y for x,y in zip(a,b)]
def scale(a,c):return [x*c for x in a]

def run():
    counts={'exact_abel':0,'exact_paired_variation_bound':0,'exact_original_line':0,'exact_negative_controls':0}
    for q in (1,2,3,4,5,8,11):
      for c in (-7,-1,0,1,3,11):
       for N in (0,1,2,5,9):
        for g in (lambda j:j*j-3*j+1,lambda j:(-1)**j*(j+1),lambda j:0):
         f=lambda j:phase(q,c*j)
         prefix=lambda n:[sum(f(j)[r] for j in range(n)) for r in range(q)]
         lhs=[sum(g(j)*f(j)[r] for j in range(N+1)) for r in range(q)]
         rhs=scale(prefix(N+1),g(N))
         for j in range(N):rhs=padd(rhs,scale(prefix(j+1),g(j)-g(j+1)))
         assert lhs==rhs;counts['exact_abel']+=1
    for N in (0,1,2,5,9):
      for shift in (-5,-1,0,1,4):
       u=lambda j:(j+shift)**2-3*(j+shift)+1
       v=lambda j:(-1)**j*(j+2)
       a=max(abs(u(j)) for j in range(N+1));b=max(abs(v(j)) for j in range(N+1))
       vu=sum(abs(u(j)-u(j+1)) for j in range(N))
       vv=sum(abs(v(j)-v(j+1)) for j in range(N))
       actual=abs(u(N)*v(N))+sum(abs(u(j)*v(j)-u(j+1)*v(j+1)) for j in range(N))
       assert actual<=a*b+a*vv+b*vu;counts['exact_paired_variation_bound']+=1
    for q in (1,2,3,4,5,8,11):
      for k in (-7,-1,0,1,3):
       for y,h,v in [((1,-2,0,3,1),(2,1,0,-1,3),(1,0,0,0,0)),
                     ((0,1,2,-1,3),(-2,1,1,0,2),(2,-1,1,3,-2)),
                     ((1,0,0,0,0),(0,0,0,0,0),(0,0,0,0,0))]:
        for N in (0,1,2,5,9):
         lhs=[0]*q;rhs=[0]*q
         for j in range(N):
          z=line(y,v,j);zh=add(h,z);g=W(zh)*W(z)
          actual=Q(k,zh)-Q(k,z);expected=Q(k,h)+2*B(k,h,y)+2*B(k,h,v)*j
          assert actual==expected
          lhs=padd(lhs,phase(q,actual,g));rhs=padd(rhs,phase(q,expected,g))
         assert lhs==rhs;counts['exact_original_line']+=1
    # Missing endpoint and omitting one factor's variation are detected.
    assert sum((j+1)*(j+2) for j in range(4)) != sum(((j+1)-(j+2))*sum(i+2 for i in range(j+1)) for j in range(3))
    u=[1,4];v=[1,1]
    assert abs(u[1]*v[1])+abs(u[0]*v[0]-u[1]*v[1])>max(u)*max(v)
    counts['exact_negative_controls']=2
    numerical=0
    for q in range(1,101):
      for r in range(q):
        x=r/q
        if x>0.5:x-=1
        chord=abs(complex(math.cos(2*math.pi*x),math.sin(2*math.pi*x))-1)
        assert 4*abs(x)<=chord+1e-12
        if x:
          assert 2/chord<=1/(2*abs(x))+1e-9
        numerical+=1
    result={'status':'PASS','scope':'Exact finite integer polynomial identities and variation inequalities; numerical chord sanity explicitly separate. Not Lean, rational-approximation summation or minor-arc decay verification.','exact_checks':counts,'numerical_chord_checks':numerical}
    Path(__file__).with_name('ABEL-REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
