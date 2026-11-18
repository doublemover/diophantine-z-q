from itertools import product
import json
def v(x,p):
 v=0
 while x and x%p==0:x//=p;v+=1
 return v,x
def cls(x,p):
 a,x=v(x,p);return a%2,x%(8 if p==2 else 3)
def issq(x,p):return cls(x,p)==(0,1)
def table(p):
 reps=[1,3,5,7,2,6,10,14] if p==2 else [1,2,3,6]
 mod=256 if p==2 else 243
 def can(B,t):
  if issq(t,p) or issq(-3*t,p):return True # simple affine branch, t≠0
  # projective primitive U,V. Scale unit denominator to 1 (or numerator to 1 if p|V)
  # includes 0 and infinity, removable by smoothness.
  for x in range(mod):
   for U,V in [(x,1),(1,p*x)]:
    a=V*V-t*U*U;c=V*V+3*t*U*U;z=B*a*c
    assert a and c and max(v(a,p)[0],v(c,p)[0])<=2
    if issq(z,p):return True
  return False
 ret=[]
 for B in reps:
  S={cls(t,p) for t in reps if can(B,t)}
  mul=lambda x,y:cls((p**x[0]*x[1])*(p**y[0]*y[1]),p)
  SS={mul(x,y) for x,y in product(S,repeat=2)}
  ret.append(dict(B=B,one_slot=[t for t in reps if cls(t,p) in S],unrestricted=[t for t in reps if cls(t,p) in SS],plus=[t for t in reps if cls(t,p) in S],minus=[t for t in reps if mul(cls(-3,p),cls(t,p)) in S]))
 return ret
if __name__=='__main__':print(json.dumps({p:table(p) for p in [2,3]},indent=2))
