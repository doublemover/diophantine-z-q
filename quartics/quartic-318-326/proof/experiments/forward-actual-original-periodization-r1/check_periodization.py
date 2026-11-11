"""Independent finite/quad regression, not a proof of the Lean statements."""
import cmath,itertools,json

def tent(x):return max(0.,1-abs(x))
def weight(x,c):return tent(x)*cmath.exp(2j*cmath.pi*c*x*x)
def trap(f,a,b,n=2000):
 h=(b-a)/n
 return h*(sum(f(a+i*h) for i in range(1,n))+(f(a)+f(b))/2)
def check():
 tests=0;errors=[]
 for k in (318,326):
  coeffs=(1,1,-1,-1,-k)
  for beta in (0.,0.001):
   for m in ((0,0,0,0,0),(1,-1,2,0,1)):
    lhs=rhs=1+0j
    for c,n in zip(coeffs,m):
     f=lambda x:weight(x,beta*c)
     P=lambda x:sum(f(x+z) for z in range(-3,4))
     for x in (0.,.125,.5,.875,1.):
      assert abs(P(x)-P(x+1))<1e-12
      assert abs(sum(cmath.exp(-2j*cmath.pi*n*(x+z))*f(x+z) for z in range(-3,4))-cmath.exp(-2j*cmath.pi*n*x)*P(x))<1e-12
     lhs*=trap(lambda x:cmath.exp(-2j*cmath.pi*n*x)*P(x),0,1)
     rhs*=trap(lambda x:cmath.exp(-2j*cmath.pi*n*x)*f(x),-1,1)
    err=abs(lhs-rhs);assert err<1e-5;errors.append(err);tests+=1
 return {'original_five_coordinate_coefficient_tests':tests,'max_quadrature_error':max(errors),'status':'PASS numerical regression only'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
