"""Exact rational sanity checks only, not Lean or theorem validation."""
from pathlib import Path
from fractions import Fraction as F
import ast,json,re
text=(Path(__file__).parent/'primary-sources/Raw318FinalReplayData.lean').read_text()
rows={int(n):re.sub(r'w (\d+)',r'w[\1]',e) for n,e in re.findall(r'def r(\d+) \(S : ℚ\) \(w : Assignment\) : ℚ := ([^\n]+)',text) if 263<=int(n)<=281}
def evaluate(node,w):
 if isinstance(node,ast.Expression):return evaluate(node.body,w)
 if isinstance(node,ast.Constant):return F(node.value)
 if isinstance(node,ast.Subscript) and isinstance(node.value,ast.Name) and node.value.id=='w':return w[node.slice.value]
 if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return -evaluate(node.operand,w)
 if isinstance(node,ast.BinOp):
  a,b=evaluate(node.left,w),evaluate(node.right,w)
  if isinstance(node.op,ast.Add):return a+b
  if isinstance(node.op,ast.Sub):return a-b
  if isinstance(node.op,ast.Mult):return a*b
  if isinstance(node.op,ast.Div):return a/b
 raise ValueError(ast.dump(node))
parsed={n:ast.parse(e,mode='eval') for n,e in rows.items() if n not in [272,273]}
count=0
for q in map(F,[-2,-1,0,1,3]):
 for f in [F(-1),F(0),F(1,3),F(1)]:
  for H in [F(-2),F(-1,2),F(1),F(3,2)]:
   x=q+q*q;four=x*x+F(496408687,100291113)*x**3+F(197130368,33430371)*x**4
   r=101783690143177584*x+267108917866935984*x*x+533801448346128768*four+4376874610839020
   norm=F(2);invnorm=1/norm;N=1+(H/r)**2+2*f/r;Q=invnorm/(H*r**15);W=N*N+r*Q*Q;den=1+114444*r;quot=W/den
   w={0:q,33:f,37:H,82:F(3),83:F(-1),118:q*q,296:x*x,297:four,298:1/r,299:1/r**2,300:1/r**4,301:1/r**8,302:1/r**16,303:F(2),304:F(1),305:F(4),306:F(1),307:norm,308:invnorm,309:H/r,310:Q,311:N-1,312:Q*Q,313:quot,314:114444*r*quot*quot}
   for n,node in parsed.items():assert evaluate(node,w)==0,(n,q,f,H)
   assert den*quot==W
   assert -1-2*(N-1)-(N-1)**2-r*Q*Q+den*quot==0
   count+=1
print(json.dumps({'status':'PASS_EXACT_RATIONAL_SAMPLES_ONLY','samples':count,'rows':sorted(parsed),'excluded_rows':{'272':'Unchanged Kummer real component; needs actual root relation','273':'Unchanged Kummer imaginary component; needs actual root relation'},'lean_run':False,'proof_acceptance':False},indent=2))
