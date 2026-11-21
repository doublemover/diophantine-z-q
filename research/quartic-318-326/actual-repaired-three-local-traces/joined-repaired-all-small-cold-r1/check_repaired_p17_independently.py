import json,sys
from fractions import Fraction as Q
from math import prod
from pathlib import Path
primary=json.loads(Path(sys.argv[1]).read_bytes()); reviewed=json.loads(Path(sys.argv[2]).read_bytes())
p=17; M=p*p; J=int(primary['literal_J']); S=1+6**15*3**65536*J; k=2*(S-2)
h=int(primary['final_h'])
assert (h%20,h%M)==(0,204)
def mat(x,y,n):
 a,b,c,d=x;e,f,g,h=y
 return ((a*e+b*g)%n,(a*f+b*h)%n,(c*e+d*g)%n,(c*f+d*h)%n)
def uv(z,n):
 A=(0,1,n-1,z%n); R=(1,0,0,1)
 for bit in reversed(bin(k)[2:]):
  if bit=='1':R=mat(A,R,n)
  A=mat(A,A,n)
 return R[1],R[3]
def red(a,n=M):
 a=Q(a);return a.numerator*pow(a.denominator,-1,n)%n
def v(a):
 a=Q(a);assert a; i=0
 while a.numerator%p==0:a/=p;i+=1
 while a.denominator%p==0:a*=p;i-=1
 return i
arms=[]
for r in [6,11]:
 rho=next(j for j in range(r,M,p) if j*j%M==2)
 D=(3-rho)**2; R=((1+rho)%M,2*rho%M)
 def add(P,Q):
  if len(P)==1:
   if len(Q)==1:return ((P[0]+Q[0])%M,)
   zz=P[0];x,y=Q
   return ((x+2*y*zz)%M,(y+(3*x*x-D)*zz)%M)
  if len(Q)==1:return add(Q,P)
  x,y=P; u,t=Q
  jac=u*u+u*x+x*x-D
  if (u-x)%p: w=red(__import__('fractions').Fraction(t-y,u-x))
  elif (t-y)%p: return (red(__import__('fractions').Fraction(u-x,t-y)),)
  elif (t+y)%p: w=red(__import__('fractions').Fraction(jac,t+y))
  else: return (red(__import__('fractions').Fraction(t+y,jac)),)
  xx=(w*w-x-u)%M
  return (xx,(w*(x-xx)-y)%M)
 assert (R[1]**2-R[0]**3+D*R[0])%M==0
 seq=[(0,)]
 for _ in range(17*32):seq.append(add(R,seq[-1]))
 order=next(i for i,t in enumerate(seq[1:],1) if len(t)==1)
 o=order*p
 assert seq[o]==(0,) and v(seq[order][0])==1
 d=S-2; lam=1
 for pp in (2,5,17):
  if not o%pp:
   while not d%pp:d//=pp;lam*=pp
 from math import gcd
 assert lam*d==S-2 and gcd(d,o)==1
 u,V=uv(S,o*lam);assert not u%lam
 ls=tuple(j%o for j in (3723,S,V,u//lam*pow(d,-1,o)))
 Uv=[];Vv=[]
 for j in ls:
  x,y=seq[j]
  Uv.append(red(Q(2*y,x*x+D)))
  Vv.append(red(Q(x**4-6*D*x*x+D*D,(x*x+D)**2)))
 assert all(u%p for u in Uv)
 Qj=[red(1+Q(5,13)*(vv-1)) for vv in Vv]
 assert all(u%p for u in Qj[1:])
 alpha=red(-1+7*Q(rho,4));m=red(Q(39,8)-Q(9*rho,2)); y=red(Q(D,alpha**4),p)
 Pg=red(1-Q(61,65)*y+Q(16,195)*y*y,p);Qg=red(1-Q(7,13)*y,p)
 assert Pg*Qg%p
 prod_inv=pow(prod(Uv),-1,M)
 row=dict(r=r,root=rho,order=order,formal_z_at_order=seq[order][0],literal_labels=list(ls),U_p2=Uv,V_p2=Vv,QJ_p2=Qj,Padé_p=[Pg,Qg],product=prod_inv)
 old=reviewed['arms'][len(arms)]
 for z in ('r','root','order','formal_z_at_order','literal_labels','U_p2','V_p2','QJ_p2'):assert row[z]==old[z]
 assert [Pg,Qg]==old['PG_QG_p'] and v(m)==old['m_depth']
 arms.append(row)
P,Q0=[z['product'] for z in arms]
scales=[1,red(Q(P+Q0,2)+P*Q0),P*Q0%M]; assert scales==reviewed['c_p2']==[1,216,84]
assert all(pow(int(primary[z])%p,8,p)==1 for z in ('a','b'))
roots=(0,Q(-1,2),-1,Q(-32,407),Q(1,2399))
depths=[]
for c in scales:
 W=Q(1,p);T=(Q(c,scales[1])*W)**2
 F=prod(T-s for s in roots); Delta=T-1; w=c**10*Delta**2/F
 assert v(F)==-10 and red(F*p**10,p) in {r*r%p for r in range(1,p)}
 assert (v(w),v(w**7*Delta**18),v(w**25*Delta**72))==(6,6,6)
 assert v(1/(F*Delta**(-6)))==-2
 depths.append(v(F)+2*v(Q(1,2))-6*v(Delta))
assert depths==[2,2,2]
print(json.dumps(dict(h_mod_289=204,arms=arms,scale_mod_289=scales,weight_depth=6,pole_depths=depths),indent=2,ensure_ascii=False))
