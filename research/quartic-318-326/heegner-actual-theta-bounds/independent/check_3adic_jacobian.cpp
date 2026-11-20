#include <gmpxx.h>
#include <iostream>
#include <cassert>
#include <algorithm>
using Z=mpz_class;
using namespace std;
Z mod(const Z &x,const Z &m){ Z y; mpz_mod(y.get_mpz_t(),x.get_mpz_t(),m.get_mpz_t()); return y; }
Z p3(int n){ Z y; mpz_ui_pow_ui(y.get_mpz_t(),3,n); return y; }
Z inv(const Z &x,const Z &m){ Z y; assert(mpz_invert(y.get_mpz_t(),x.get_mpz_t(),m.get_mpz_t()));return y; }
int N=0;
Z modP;
int vp(Z a){ if(a==0) return N; int n=0; while(a%3==0){a/=3;++n;}return n; }
struct F{ Z a,b; F(Z a=0,Z b=0):a(mod(a,modP)),b(mod(b,modP)){}
 F operator+(const F&o)const{return F(a+o.a,b+o.b);}
 F operator-(const F&o)const{return F(a-o.a,b-o.b);}
 F operator*(const F&o)const{return F(a*o.a+2*b*o.b,a*o.b+b*o.a);}
 F scale(int n)const{return F(n*a,n*b);}
 F sq()const{return *this**this;}
 int val()const{return min(vp(a),vp(b));}
};
struct Pt{F x,y,z;};
Pt normalize(Pt t){
 int n=min({t.x.val()/2,t.y.val()/3,t.z.val()});
 if (!n)return t;
 assert(n>0 && N-3*n>=262188);
 N-=3*n;modP=p3(N);
 return {F(t.x.a/p3(2*n),t.x.b/p3(2*n)),F(t.y.a/p3(3*n),t.y.b/p3(3*n)),F(t.z.a/p3(n),t.z.b/p3(n))};
}
int main(){
 int K=262188; N=K+512;modP=p3(N);
 F d(3,-1), aa=F(0)-d.sq(), r(1,1), s(0,2);
 const Z h("473592745039516333133760"),A("500907037962860804880"),R("4376874610839020"),B("204618888056724185");
 const Z idx("15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000");
 Z pow6;mpz_ui_pow_ui(pow6.get_mpz_t(),6,15);
 Z num=pow6*p3(65536)*idx; assert(num%h==0);
 Z m=num/h; mpz_class u3=3, q3;
 auto v=mpz_remove(q3.get_mpz_t(),m.get_mpz_t(),u3.get_mpz_t()); assert(v==65547);
 Pt t{r,s,F(1)};
 auto dh=h.get_str(2);
 for(size_t j=1;j<dh.size();++j){
  F yy=t.y.sq(), S=(t.x*yy).scale(4), M=t.x.sq().scale(3)+aa*t.z.sq().sq();
  F X=M.sq()-S.scale(2), Y=M*(S-X)-yy.sq().scale(8), ZZ=(t.y*t.z).scale(2);
  t=normalize({X,Y,ZZ});
  if(dh[j]=='1'){
   F zz=t.z.sq(), H=r*zz-t.x, U=s*t.z*zz-t.y;
   assert(H.val()<N);
   F h2=H.sq(), h3=h2*H, xh=t.x*h2;
   F X=U.sq()-h3-xh.scale(2),Y=U*(xh-X)-t.y*h3,ZZ=t.z*H;
   t=normalize({X,Y,ZZ});
  }
 }
 assert(t.z.val()>0 && t.x.val()==0 && t.y.val()==0);
 F den=t.x.sq()+d.sq()*t.z.sq().sq();
 assert(den.val()==0);
 F invden=F(den.a,-den.b)*F(inv(den.a*den.a-2*den.b*den.b,modP));
 F u=(t.y*t.z).scale(2)*invden;
 assert(u.val()==5);
 Z modK=p3(K), rinv=inv(R,modK);
 Z H=mod(u.a*u.a-2*u.b*u.b,modK), f=mod(u.a*u.a+2*u.b*u.b,modK);
 Z j=mod(H*rinv,modK), n=mod(1+j*j+2*f*rinv,modK), W=mod(n*n,modK);
 Z c=mod(12*W*inv(A+1,modK),modK), delta=mod(1-B*c*c,modK);
 cout<<delta.get_str(16)<<"\n";
 cerr<<"projective precision "<<N<<" v(Z) "<<t.z.val()<<" v(U) "<<u.val()<<endl;
}
