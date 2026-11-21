// Actual scalar, compressed p=3 arithmetic. No expanded elliptic coordinates.
// Build: g++ -std=c++17 -O3 bound_actual_scalar_expanded_input.cpp -lgmpxx -lgmp
#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <gmpxx.h>
#include <iostream>
#include <string>
using Z=mpz_class;
constexpr int DEFAULT_K=262188;
int P=DEFAULT_K+512;
Z pow3(int r){
 assert(r>=0);
 Z t;mpz_ui_pow_ui(t.get_mpz_t(),3,r);return t;
}
Z mod(const Z&a,const Z&n){
 Z t;mpz_mod(t.get_mpz_t(),a.get_mpz_t(),n.get_mpz_t());return t;
}
Z inv(const Z&a,const Z&n){
 Z t;int ans=mpz_invert(t.get_mpz_t(),a.get_mpz_t(),n.get_mpz_t());
 assert(ans!=0);return t;
}
Z gcd(Z a,Z b){
 Z t;mpz_gcd(t.get_mpz_t(),a.get_mpz_t(),b.get_mpz_t());return t;
}
Z sqrt_floor(Z a){
 Z t;mpz_sqrt(t.get_mpz_t(),a.get_mpz_t());return t;
}
int bits(Z a){return mpz_sizeinbase(a.get_mpz_t(),2);}
struct V{
 // 3^e*(a+b*sqrt2) + O(3^N), N is absolute.
 Z a,b;int e,N;
 V(Z a=0,Z b=0,int e=0,int N=P):a(a),b(b),e(e),N(N){
   assert(N>=e);
   Z q=pow3(N-e);this->a=mod(this->a,q);this->b=mod(this->b,q);
   if(this->a==0 && this->b==0){this->e=N;return;}
   while(this->a%3==0 && this->b%3==0){
     this->a/=3;this->b/=3;++this->e;
   }
 }
 V operator+(const V&y)const {
   int d=std::min(e,y.e),M=std::min(N,y.N);
   Z p=pow3(e-d),q=pow3(y.e-d);
   return V(p*a+q*y.a,p*b+q*y.b,d,M);
 }
 V operator-()const{return V(-a,-b,e,N);}
 V operator-(const V&y)const{return *this+-y;}
 V operator*(const V&y)const {
   return V(a*y.a+2*b*y.b,a*y.b+b*y.a,e+y.e,std::min(N+y.e,y.N+e));
 }
 V operator/(const V&y)const {
   int d=y.N-y.e;assert(d>0);
   // The norm of a residual unit is a unit because Q_3(sqrt2) is unramified.
   Z u=inv(y.a*y.a-2*y.b*y.b,pow3(d));
   return *this*V(u*y.a,-u*y.b,-y.e,d-y.e);
 }
};

int main(int argc,char**argv){
 int K=argc>1?std::atoi(argv[1]):DEFAULT_K;
 assert(K>=1 && K<=DEFAULT_K);P=K+512;
 Z h("473592745039516333133760");
 Z j("15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000");
 Z R("4376874610839020"),A("500907037962860804880"),b("204618888056724185");
 assert(h%81==0 && h%243!=0 && j%3!=0 && R%3!=0 && (A+1)%3!=0);
 const V s(0,1), d=V(3)-s, Q=d*d, rx=V(1)+s, ry=V(2)*s;
 V x=rx,y=ry;
 const auto digits=h.get_str(2);
 for(size_t k=1;k<digits.size();k++){
   V m=(V(3)*x*x-Q)/(V(2)*y), X=m*m-V(2)*x;
   y=m*(x-X)-y;x=X;
   if(digits[k]=='1'){
     m=(y-ry)/(x-rx);X=m*m-x-rx;
     y=m*(x-X)-y;x=X;
   }
 }
 V u=V(2)*y/(x*x+Q);
 assert(u.N>=K && u.e>=1 && u.N>u.e);
 // U(h) in the formal group. Actual m=i/h has v_3=65547, so v_3(Q_scalar)>=131094,
 // W=N_scalar^2 mod 3^262188. Compute its actual low terms without i.
 Z M=pow3(K), a=mod(u.a*pow3(u.e),M), z=mod(u.b*pow3(u.e),M);
 Z H=mod(a*a-2*z*z,M),f=mod(a*a+2*z*z,M);
 Z ri=inv(R,M),v=mod(H*ri,M),N=mod(1+v*v+2*f*ri,M),W=mod(N*N,M);
 Z c=mod(12*W*inv(A+1,M),M),delta=mod(1-b*c*c,M);
 assert(delta%3==1);
 Z bound=sqrt_floor((M-1)/2);
 // If 0<H0<Z0^2<=bound and delta*Z0^2 == H0 (mod M), the reduced
 // fraction k/Z0^2 is a convergent of delta/M: error < 1/(2*(Z0^2)^2).
 // Recursively compute the signed remainder in parallel with convergent
 // denominators. This avoids forming their dense products at each step.
 Z E0=delta,E1=M, den0=0,den1=1;
 // Initialize first Euclidean step (quotient zero) in the recurrence;
 // convergent numerators/denominators start with 0/1 for delta/M<1.
 Z rem_prev=-M,rem=delta;
 Z b_prev=0,b_curr=1;
 int tested=0,low_height=0,compatible=0;
 while(b_curr<=bound){
   // rem is the signed delta*b_curr - M*next approximation numerator.
   if(rem>0 && rem<b_curr && rem<=bound && 9*rem>8*b_curr &&
      mpz_perfect_square_p(b_curr.get_mpz_t()) && gcd(rem,b_curr)==1)
      ++compatible;
   if(rem>0 && rem<=bound)++low_height;
   ++tested;
   if(rem==0)break;
   Z quo=(-rem_prev)/rem;
   assert(quo>=0);
   Z next=rem_prev+quo*rem;
   Z b_next=b_prev+quo*b_curr;
   rem_prev=rem;rem=next;b_prev=b_curr;b_curr=b_next;
 }
 assert(compatible==0);
 Z Hlo=8*bound/9+1;
 std::cout<<"k "<<K<<" modulus_bits "<<bits(M)<<" chart_abs_precision "<<u.N
          <<" chart_valuation "<<u.e<<" convergents "<<tested
          <<" positive_bounded_remainders "<<low_height<<" compatible "<<compatible
          <<" denom_valuation_at_3 0 lower_H_bitlength "<<bits(Hlo)<<'\n';
 if(argc>2) std::cout<<delta.get_str(16)<<'\n';
}
