import itertools,json
p=5
S=list(itertools.product(range(p),repeat=2))
add=lambda x,y:tuple((a+b)%p for a,b in zip(x,y))
neg=lambda x:tuple(-a%p for a in x)
mul=lambda x,y:tuple(a*b%p for a,b in zip(x,y))
tau=lambda x:x[::-1]
zero=(0,0); one=(1,1)
A=list(itertools.product(S,repeat=2))
am=lambda x,y:(mul(x[0],y[0]),add(mul(x[0],y[1]),mul(x[1],y[0])))
fval=lambda f,x:add(mul(f[0],x[0]),mul(f[1],x[1]))
t=(1,2); k=neg(mul(t,t))
# B is the SAME ring carrier with reciprocal S action s*x=tau(s)*x.
def trans(f,x):return tau(fval(f,x))
counts={'all_functional_values':0,'scalar_compatibilities':0,'order_actions':0,'differential_values':0}
for f in A:
 for x in A:
  assert tau(trans(f,x))==fval(f,x)
  counts['all_functional_values']+=1
  assert trans(f,am((k,zero),x))==mul(tau(k),trans(f,x))
  counts['differential_values']+=1
 for s in S:
  for x in [A[1],A[6],A[100],A[321]]:
   scaled=(mul(tau(s),x[0]),mul(tau(s),x[1]))
   assert trans(f,scaled)==mul(s,trans(f,x))
   counts['scalar_compatibilities']+=1
 for a in [A[1],A[6],A[100],A[321]]:
  # whole order precomposition; f_a determined by values on 1,epsilon
  fa=(fval(f,a),fval(f,(zero,a[0])))
  for x in [A[1],A[6],A[100],A[321]]:
   assert trans(fa,x)==trans(f,am(a,x))
   counts['order_actions']+=1
f=((1,2),(3,4));x=((2,1),(1,3))
assert any(fval(f,((mul(tau(s),x[0])),mul(tau(s),x[1])))!=mul(s,fval(f,x)) for s in S)
assert any(trans(f,am((k,zero),x))!=trans(f,x) for x in A)
assert any(trans(f,am((k,zero),x))!=mul(tau(mul(t,t)),trans(f,x)) for x in A)
assert any(trans(f,am((k,zero),x))!=mul(tau(neg(t)),trans(f,x)) for x in A)
print(json.dumps({'status':'PASS','counts':counts,'negative_controls':4,'scope':'finite exact dual-number/split-base algebra sanity checks, not Lean or categorical proof'},indent=2))
