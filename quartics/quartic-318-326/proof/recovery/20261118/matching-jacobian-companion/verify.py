from fractions import Fraction as F
import json
def check(B,T,k):
 def Q(a,b=0):return F(a),F(b)
 def add(x,y):return x[0]+y[0],x[1]+y[1]
 def neg(x):return -x[0],-x[1]
 def sub(x,y):return add(x,neg(y))
 def mul(x,y):return x[0]*y[0]+B*x[1]*y[1],x[0]*y[1]+x[1]*y[0]
 def inv(x):
  n=x[0]**2-B*x[1]**2;return x[0]/n,-x[1]/n
 def div(x,y):return mul(x,inv(y))
 m=B*k*k;C=T*(1-m);g=Q(-9*C*B**2*(m-9));a=inv(Q(0,3));b=neg(a)
 def pre(s):return div(sub(s,Q(k)),sub(Q(1),mul(Q(B*k),s)))
 c=pre(a);d=pre(b);A=mul(g,mul(sub(a,b),mul(sub(a,c),sub(a,d))))
 U=lambda x:neg(inv(sub(a,x)))
 r1=B*C*(25*m-9);r2=16*B*C*m
 assert div(mul(A,sub(U(c),U(b))),Q(4))==Q(r1)
 assert div(mul(A,sub(U(d),U(b))),Q(4))==Q(r2)
 for x in [F(0),F(1,13),F(-4,11),F(9)]:
  y2=C*(1-9*B*x*x)*((1+B*k*x)**2-9*B*(x+k)**2)
  u=inv(sub(Q(x),a));X=div(mul(A,sub(u,U(b))),Q(4))
  ysq=mul(Q(y2),mul(mul(A,A),mul(mul(u,u),mul(u,u))))
  assert div(ysq,Q(64))==mul(X,mul(sub(X,Q(r1)),sub(X,Q(r2))))
def main():
 count=0
 for b in (17,41,73,17*41):
  for th in (1,409,457):
   for k in (4,12):check(b,th,k);count+=1
 print(json.dumps({'quadratic_field_model_checks':count,'affine_chart_checks':4*count},indent=2))
if __name__=='__main__':main()
