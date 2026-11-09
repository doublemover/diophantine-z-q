from pathlib import Path
import re,json
import sympy as S
raw=Path('quartics/quartic-318-326/proof/318/Raw318FinalReplayData.lean').read_text();w=S.symbols('w0:400')
def pair(a,b=0):return (S.sympify(a),S.sympify(b))
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def neg(a):return(-a[0],-a[1])
def sub(a,b):return add(a,neg(b))
def mul(a,b):return(a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(c,a):return(c*a[0],c*a[1])
def pow(a,n):
 b=pair(1)
 for _ in range(n):b=mul(a,b)
 return b
def PG(x):return add(sub(pair(1),scale(S.Rational(61,65),x)),scale(S.Rational(16,195),pow(x,2)))
def QG(x):return sub(pair(1),scale(S.Rational(7,13),x))
def PJ(x):return sub(add(pair(1),scale(S.Rational(12,65),x)),scale(S.Rational(2,195),pow(x,2)))
def QJ(x):return add(pair(1),scale(S.Rational(5,13),x))
k=pair(-1,S.Rational(7,4));m=pair(S.Rational(39,8),-S.Rational(9,2));D=pair(11,-6);s=pair(w[35],w[36]);F=pair(w[76],w[77]);mid=pair(w[74],w[75]);A=add(add(m,mul(pow(k,2),s)),mul(D,mid));B=add(add(pow(k,2),mul(m,s)),mul(D,F));arg=mul(D,pow(F,2))
p=pair(*S.symbols('p0 p1'));c=pair(*S.symbols('c0 c1'));J=[pair(*S.symbols(f'j{i}r j{i}i')) for i in range(4)];L=[pair(*S.symbols(f'l{i}r l{i}i')) for i in range(4)];R=[pair(*S.symbols(f'r{i}r r{i}i')) for i in range(4)]
u=lambda j:pair(w[4*j+1],w[4*j+2]);v=lambda j:pair(w[4*j+3],w[4*j+4]);J[0]=sub(pair(1),scale(S.Rational(1,5),sub(v(4),pair(1))))
repl={w[90]:pow(F,2)[0],w[91]:F[0]*F[1],w[92]:p[0],w[93]:p[1],w[94]:c[0],w[95]:c[1]}
for i in range(1,4):repl[w[94+2*i]]=J[i][0];repl[w[95+2*i]]=J[i][1]
for i in range(4):
 for a,idx in [(L[i],102+4*i),(R[i],104+4*i)]:repl[w[idx]]=a[0];repl[w[idx+1]]=a[1]
expected={51:S.Integer(0),52:S.Integer(0)}
blocks={53:sub(mul(QG(arg),p),PG(arg)),55:sub(mul(B,c),mul(mul(k,s),p))}
for i in range(1,4):blocks[55+2*i]=sub(mul(QJ(sub(v(i+4),pair(1))),J[i]),PJ(sub(v(i+4),pair(1))))
for i in range(4):blocks[63+4*i]=sub(mul(mul(k,v(i)),L[i]),mul(u(i),A));blocks[65+4*i]=add(mul(c,R[i]),mul(u(i+4),J[i]))
for i,a in blocks.items():expected[i]=a[0];expected[i+1]=a[1]
for i in range(51,79):
 e=re.search(r'@\[expose\] def r'+str(i)+r' \(S : ℚ\) \(w : Assignment\) : ℚ := (.*)',raw).group(1);e=re.sub(r'w (\d+)',r'w\1',e);expr=S.sympify(e,locals={f'w{j}':x for j,x in enumerate(w)},rational=True).subs(repl,simultaneous=True)
 delta=S.expand(expr-expected[i]);assert delta==0,(i,delta)
print('PASS: all 28 literal rows51–78 agree exactly with the proved field identities, coefficient for coefficient.')
# Every detector gate uses earlier stored coordinates only. Forward evaluation
# kills its literal residual; neither preceding block is overwritten.
for stop,bound in [(51,90),(79,118)]:
 for i in range(stop):
  e=re.search(r'@\[expose\] def r'+str(i)+r' \(S : ℚ\) \(w : Assignment\) : ℚ := (.*)',raw).group(1)
  assert all(int(x)<bound for x in re.findall(r'\bw (\d+)',e)),(i,bound)
gates={}
for i in range(79,107):
 e=re.search(r'@\[expose\] def r'+str(i)+r' \(S : ℚ\) \(w : Assignment\) : ℚ := (.*)',raw).group(1)
 out=int(re.search(r'\+ \(1 \* w (\d+)\)$',e).group(1))
 assert out==i+39
 before=e[:e.rfind(' + (1 * w ')]
 assert all(int(x)<out for x in re.findall(r'\bw (\d+)',before))
 expr=S.sympify(re.sub(r'w (\d+)',r'w\1',e),locals={f'w{j}':x for j,x in enumerate(w)},rational=True)
 value=-expr.subs(w[out],0)
 assert S.expand(expr.subs(w[out],value))==0
 gates[out]=str(value)
print('PASS: all28 detector gates are triangular literal row evaluations; first51/first79 coordinate supports are preserved.')
