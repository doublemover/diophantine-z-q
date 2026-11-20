// Exact finite-field scan of the literal scalar from the frozen a=0 h,J.
// Proposed annihilators are always checked before reducing indices.
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using I=int64_t; using UI=__uint128_t;
const std::string a_str="500907037962860804880", h_str="473592745039516333133760",
J_str="15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000";
const std::string reduced_J="2566827915619116471899843747792873596324159383802094955344492089413795992750334532240167202776488314896151365217289774312203906250";
const I B=204618888056724185LL,R=4376874610839020LL;

I md(I x,I q){x%=q;return x<0?x+q:x;}
I mult(I a,I b,I q){return (UI(a)*b)%q;}
I powm(I a,I n,I q){I x=1;for(;n;n>>=1){if(n&1)x=mult(x,a,q);a=mult(a,a,q);}return x;}
I scan_str(const std::string&s,I q){I a=0;for(char c:s)a=mult(a,10,q)+(c-'0'),a%=q;return a;}
I shift(I o){return mult(mult(powm(6,15,o),powm(3,65536,o),o),scan_str(J_str,o),o);}
I mm(I p){return mult(mult(powm(6,15,p),powm(3,65532,p),p),scan_str(reduced_J,p),p);}
I inv(I a,I q){
    I b=q,s=1,t=0;
    while(b){I c=a/b; I r=a-c*b; a=b;b=r; r=s-c*t;s=t;t=r;}
    assert(a==1);return md(s,q);
}
int chis(I a,I p){I x=powm(md(a,p),(p-1)/2,p);return x==p-1?-1:(int)x;}
I sqrtm(I a,I p){
    if(chis(a,p)!=1)return -1;
    if((p&3)==3)return powm(a,(p+1)/4,p);
    I d=p-1;int s=0;while(d%2==0)d/=2,++s;
    I z=2;while(chis(z,p)!=-1)++z;
    I x=powm(a,(d+1)/2,p),b=powm(a,d,p),g=powm(z,d,p);
    while(b!=1){int j=1;I q=mult(b,b,p);while(q!=1)q=mult(q,q,p),++j;assert(j<s);
      I z=powm(g,1LL<<(s-j-1),p);x=mult(x,z,p);g=mult(z,z,p);b=mult(b,g,p);s=j;}
    assert(mult(x,x,p)==a);return x;
}
I odd_gaussian_coord(I p){
    I b=sqrtm(p-1,p);
    for(I g:{b,p-b}){I a=p;while(g*g>p){I c=a%g;a=g;g=c;}
      I w=(I)std::sqrt(double(p-g*g));
      while((w+1)*(w+1)<=p-g*g)++w;while(w*w>p-g*g)--w;
      if(w*w+g*g==p)return (w&1)?w:g;
    } return -1;
}
struct F {I a,b;bool operator==(F f) const{return a==f.a&&b==f.b;}};
struct Point {F x,y;bool zero;};
struct E {
 I p, d;
 F D;
 Point r;
 F field(I a)const{return {md(a,p),0};}
 F add(F x,F y)const{return {(x.a+y.a)%p,(x.b+y.b)%p};}
 F sub(F x,F y)const{return {md(x.a-y.a,p),md(x.b-y.b,p)};}
 F mul(F x,F y)const{
  return d<0?F{(x.a*y.a+2*x.b*y.b)%p,(x.a*y.b+x.b*y.a)%p}:F{(x.a*y.a)%p,0};
 }
 F inverse(F x)const {I z=inv(md(x.a*x.a-2*x.b*x.b,p),p);return {(x.a*z)%p,md(-x.b*z,p)};}
 F div(F x,F y)const{if(d>=0)return {x.a*inv(y.a,p)%p,0};return mul(x,inverse(y));}
 E(I p,I d):p(p),d(d){
   F s=d<0?F{0,1}:field(d);
   F t=sub(field(3),s);D=mul(t,t);
   r={add(field(1),s),mul(field(2),s),false};
 }
 Point plus(Point U,Point V)const {
   if(U.zero)return V;if(V.zero)return U;
   auto [x,y,_]=U;auto [X,Y,__]=V;
   F z{0,0},m;
   if(x==X){if(add(y,Y)==z)return {z,z,true};assert(y==Y);
     m=div(sub(mul(field(3),mul(x,x)),D),mul(field(2),y));}
   else m=div(sub(y,Y),sub(x,X));
   F X0=sub(sub(mul(m,m),x),X);
   return {X0,sub(mul(m,sub(x,X0)),y),false};
 }
 Point times(I n)const {
   Point S{{0,0},{0,0},true},P=r;
   while(n){if(n&1)S=plus(S,P);n>>=1;if(n)P=plus(P,P);}
   return S;
 }
 // -1 exact finite reduction pole, 0 zero, 1 unit; point overload
 int chart(Point P,F&f)const{
   if(P.zero){f={0,0};return 0;}
   F den=add(mul(P.x,P.x),D);
   if(den==F{0,0})return -1;
   f=div(mul(field(2),P.y),den);
   return f==F{0,0} ? 0 : 1;
 }
 int ratio(Point P, F u, int su, F v, int sv, I mod_mult, F &f)const{
    if(su==0){
      assert(sv==0);
      // U(P)/z([2]P) tends to -1 at O,T_0, +1 at T_+/T_-.
      // U([m]P)/z([2m]P) tends to -1 at O, since m is even.
      f=field(P.zero||P.x==F{0,0} ? mod_mult : -mod_mult);return 0;
    }
    if(su==1 && sv>=0){f=div(v,u);return 0;}
    return -1;
 }

};
int main(int count,char** args){
 I max=count>1?std::stoll(args[1]):2000000,lo=count>2?std::stoll(args[2]):10;
 assert(max<=200000000);
 std::vector<bool> prime(max+1,true);prime[0]=prime[1]=false;
 for(I i=2;i*i<=max;++i)if(prime[i])for(I j=i*i;j<=max;j+=i)prime[j]=false;
 I relevant=0,valid=0,blocked=0,bad_order=0,hits=0,formal=0,excluded_poles=0;
 for(I p=lo;p<=max;++p){
   if(!prime[p]||p<11||p==17||R%p==0||chis(B,p)!=1)continue;
   I ap=scan_str(a_str,p);if(ap==p-1)continue;
   ++relevant;
   I s=sqrtm(2,p),order;
   I c=p%4==3?0:odd_gaussian_coord(p);
   if(c<0){++bad_order;continue;}
   if(s<0)order=p*p+1-chis(7,p)*(4*c*c-2*p);
   else order=c?(p+1-2*c)*(p+1+2*c):(p+1);
   I hh=scan_str(h_str,order), ii=shift(order);
   E P(p,s); E Q(p,s<0?s:p-s);
   if(!P.times(order).zero||(s>=0&&!Q.times(order).zero)){++bad_order;continue;}
   auto Ph=P.times(hh), Pi=P.times(ii), Qh=Q.times(hh), Qi=Q.times(ii);
   F u{},v{},x{},y{},a{},b{};
   int uh=P.chart(Ph,u), vi=P.chart(Pi,v), xh=s<0?1:Q.chart(Qh,x), yi=s<0?1:Q.chart(Qi,y);
   I rinv=inv(R%p,p);
   // At an inert p no chart pole occurs. At a split p with a U(i) pole,
   // the Fp Gaussian submodule attached to R would have size at least 2^47.
   assert(vi>=0 && yi>=0);
   if(uh<0 || xh<0){
     assert(s>=0 && p>=32407);
     if(uh<0 && xh<0){++excluded_poles;continue;}
     if(uh<0)assert(vi==0);else assert(yi==0);
     if((1+mult((uh<0?x.a*x.a:u.a*u.a)%p,rinv,p))%p==0){
       ++blocked;std::cout<<"BLOCKED possible-N-cancel "<<p<<std::endl;continue;
     }
     // One h-pole, its i-depth positive; other i integral.
     // N negative (other factor nonzero mod p), Q positive, W a pole.
     ++excluded_poles;continue;
   }
   I mp=0;if(uh==0||xh==0){++formal;mp=mm(p);}
   assert(P.ratio(Ph,u,uh,v,vi,mp,a)==0);
   if(s>=0)assert(Q.ratio(Qh,x,xh,y,yi,mp,b)==0);
   I H,Ij,f,Qratio;
   if(s<0){
     H=md(u.a*u.a-2*u.b*u.b,p); Ij=md(v.a*v.a-2*v.b*v.b,p);
     f=(u.a*u.a+2*u.b*u.b)%p; Qratio=md(a.a*a.a-2*a.b*a.b,p);
   } else {
     H=(u.a*x.a)%p; Ij=(v.a*y.a)%p; f=mult((u.a*u.a+x.a*x.a)%p,(p+1)/2,p);
     Qratio=mult(a.a,b.a,p);
   }
   ++valid;
   I j=mult(H,rinv,p),nn=(1+j*j+mult(2*f%p,rinv,p))%p;
   I qq=mult(Qratio,powm(rinv,15,p),p);
   I ww=(nn*nn+mult(R%p,qq*qq%p,p))%p;
   I k=mult(ww,inv(ap+1,p),p),D=mult(mult(ap,inv(17,p),p),k*k%p,p);
   I cp=mult(12*ww%p,inv(ap+1,p),p);
   assert(D==mult(B%p,cp*cp%p,p));
   if(D==1){
     ++hits;std::cout<<"THETA_ZERO"<<" prime "<<p<<" annihilator "<<order
       <<" square2 "<<s<<" H "<<H<<" I "<<Ij<<" W "<<ww<<" c "<<cp<<" D "<<D
       <<" pmod4 "<<p%4<<" chisMinusR "<<chis(-R,p)<<std::endl;
   }
 }
 std::cout<<"theta-scan "<<lo<<" "<<max<<" relevant "<<relevant<<" valid "<<valid<<" formal_cancel_count "<<formal<<" ruled_out_poles "<<excluded_poles<<" inaccessible "<<blocked<<" bad_order "<<bad_order<<" hits "<<hits<<std::endl;
}
