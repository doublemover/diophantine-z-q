#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <string>
#include <iostream>
#include <vector>
using i64=int64_t; using u64=uint64_t;
i64 isqrt(i64 n){i64 x=sqrt((long double)n);while(x*x>n)--x;while((x+1)*(x+1)<=n)++x;return x;}
struct EC {
  i64 p,A,B;
  struct Pt {i64 x,y;};
  static constexpr Pt O{-1,0};
  EC(i64 q):p(q),A(76361%q),B((-76768LL*407)%q){if(B<0)B+=p;}
  i64 mod(i64 a) const {i64 r=a%p;return r<0?r+p:r;}
  i64 mul(i64 a,i64 b) const {return a*b%p;}
  i64 power(i64 a,i64 n) const { i64 r=1; for(;n;n>>=1,a=mul(a,a))if(n&1)r=mul(r,a);return r; }
  i64 chi(i64 a) const {i64 c=power(a,(p-1)/2);return c==p-1?-1:c;}
  i64 fr(i64 x) const { return mod(mul(x,mod(mul(x,x)+mul(A,x)+B))); }
  i64 inv(i64 d) const {
    i64 a=p,b=d,x=0,y=1;
    while(b>1){i64 q=a/b; i64 t=a-q*b;a=b;b=t;t=x-q*y;x=y;y=t;}
    assert(b==1);return mod(y);
  }
  i64 root(i64 a) const {
    if(a==0)return 0;
    if(chi(a)!=1)return -1;
    if(p%4==3)return power(a,(p+1)/4);
    i64 Q=p-1,M=0,z=2;
    while(!(Q&1)){++M;Q>>=1;}
    while(chi(z)!=-1)++z;
    i64 x=power(a,(Q+1)/2),t=power(a,Q),c=power(z,Q);
    while(t!=1){
      i64 k=1,v=mul(t,t);while(v!=1){v=mul(v,v);++k;}
      assert(k<M);i64 b=power(c,i64(1)<<(M-k-1));
      x=mul(x,b);c=mul(b,b);t=mul(t,c);M=k;
    }
    assert(mul(x,x)==a);return x;
  }
  Pt add(Pt P,Pt Q) const {
    if(P.x<0)return Q;if(Q.x<0)return P;
    i64 slope;
    if(P.x==Q.x){
      if(mod(P.y+Q.y)==0)return O;
      assert(P.y==Q.y);
      slope=mul(mod(3*mul(P.x,P.x)+2*mul(A,P.x)+B),inv(mod(2*P.y)));
    }else slope=mul(mod(Q.y-P.y),inv(mod(Q.x-P.x)));
    i64 rx=mod(mul(slope,slope)-A-P.x-Q.x);
    return {rx,mod(mul(slope,mod(P.x-rx))-P.y)};
  }
  Pt times(Pt P,i64 n) const {
    Pt R=O;
    while(n){if(n&1)R=add(R,P);n>>=1;if(n)P=add(P,P);}
    return R;
  }
  u64 key(Pt P,bool neg=false) const {
    return P.x<0?0:1+(u64)P.x*p+(neg&&P.y?p-P.y:P.y);
  }
  int direct() const {i64 s=0;for(i64 x=0;x<p;++x)s+=chi(fr(x));return -s;}
  void interval_annihilators(Pt Q,i64 L,i64 U,std::vector<i64>& ans)const{
    ans.clear();
    const i64 n=isqrt(U-L+1)+1;
    std::vector<std::pair<u64,int>> table;
    table.reserve(n);
    Pt R=O;
    for(i64 j=0;j<n;++j){table.emplace_back(key(R),j);R=add(R,Q);}
    const Pt step=R;
    std::sort(table.begin(),table.end());
    Pt S=times(Q,L);
    for(i64 i=0;L+i*n<=U;++i){
      const u64 k=key(S,true);
      auto c=std::lower_bound(table.begin(),table.end(),std::make_pair(k,0));
      for(;c!=table.end()&&c->first==k;++c){
        const i64 m=L+i*n+c->second;if(m<=U)ans.push_back(m);
      }
      S=add(S,step);
    }
    std::sort(ans.begin(),ans.end());assert(!ans.empty());
  }
  int trace(bool full_verify,i64&ndirect,i64&nextra)const{
    if(p<257){++ndirect;return direct();}
    const i64 width=isqrt(4*p);
    const i64 L=(p+1-width+3)/4,U=(p+1+width)/4;
    // Full rational 2-torsion => actual order is four times one integer here.
    std::vector<i64>C,D;
    int trials=0;
    for(i64 x=1;x<p&&trials<8;++x){
      const i64 y=root(fr(x));if(y<=0)continue;
      auto P=times({x,y},4);
      if(P.x<0)continue;
      ++trials;
      if(C.empty())interval_annihilators(P,L,U,C);
      else C.erase(std::remove_if(C.begin(),C.end(),[&](i64 m){return times(P,m).x>=0;}),C.end());
      assert(!C.empty());
      if(C.size()==1){
        int answer=p+1-4*C[0];
        if(full_verify)assert(answer==direct());
        if(trials>1)++nextra;
        return answer;
      }
    }
    // Preserves exact completeness even for small exponent/unlucky point seeds.
    // A bounded first-run caller can stop before an expensive aggregate run.
    ++ndirect;return direct();
  }
};
using Big = __int128_t;
Big floor_div(Big n,Big d){assert(d>0);return n/d-(n%d<0);}
Big ceil_div(Big n,Big d){return -floor_div(-n,d);}
std::string show(Big a){
  if(a==0)return "0";
  bool neg=a<0;
  if(neg)a=-a;
  std::string out;
  for(;a;a/=10)out.push_back(char('0'+a%10));
  if(neg)out.push_back('-');
  std::reverse(out.begin(),out.end());
  return out;
}
int main(int argc,char**argv){
  const int L=argc>1?std::atoi(argv[1]):200000;
  assert(20000<=L&&L<=64000000);
  const bool fullcheck=argc>2;
  std::vector<bool>sieve(L+1,true);
  std::vector<int>a(L+1,1);
  i64 ndirect=0,nextra=0,np=0,ntests=0;
  u64 fingerprint=0x8f7f7255ce2dccfbULL;
  std::array<std::pair<int,int>,7> bad={{{2,1},{3,-1},{5,-1},{7,1},{11,-1},{37,1},{2399,-1}}};
  for(int q=2;q<=L;++q){
    if(!sieve[q])continue;
    for(i64 k=(i64)q*q;k<=L;k+=q)sieve[k]=false;
    int t=0;bool good=true;
    for(auto [l,v]:bad)if(q==l){good=false;t=v;break;}
    if(good && q!=2207){
      auto C=EC(q);
      t=C.trace(fullcheck||q<=2000,ndirect,nextra);
      if(fullcheck||q<=2000)++ntests;
      if(q==13)assert(t==-2);
      if(q==17)assert(t==2);
      if(q==415721)assert(t==978);
    }
    ++np;
    fingerprint^=u64(q)*0xa5a3564e27f8861dULL+u64(t);
    fingerprint=(fingerprint^(fingerprint>>21))*0x100000001b3ULL;
    i64 prev=1,Aq=t;
    for(i64 power=q;power<=L;power*=q){
      const i64 next=power*q;
      for(i64 u=power;u<=L;u+=power)if(u%next)a[u]*=Aq;
      const i64 newAq=t*Aq-(good?q*prev:0);
      prev=Aq;Aq=newAq;
    }
  }
  std::vector<int> chi(2207,-1);chi[0]=0;
  for(int x=1;x<2207;++x)chi[x*x%2207]=1;
  // Rigorous outward fixed-point arithmetic. Bounds on r are certified by
  // the independent rational script; all products below fit signed 128 bits.
  constexpr Big scale=4503599627370496LL,rlo=4503598731974206LL,rhi=4503598731974207LL;
  Big wlo=scale,whi=scale,slo=0,shi=0;
  for(int n=1;n<=L;++n){
    wlo=floor_div(wlo*rlo,scale);whi=ceil_div(whi*rhi,scale);
    const Big c=2LL*a[n]*chi[n%2207];
    assert(-4LL*n<=c&&c<=4LL*n);
    slo+=floor_div(c*(c>=0?wlo:whi),n);
    shi+=ceil_div(c*(c>=0?whi:wlo),n);
  }
  std::cout<<"cutoff "<<L<<"\nprimes "<<np<<"\ndirect "<<ndirect<<"\nmultiple_points "<<nextra
           <<"\ncompared_to_direct "<<ntests<<"\nfingerprint "<<fingerprint
           <<"\npartial_sum_scale "<<show(scale)<<"\npartial_sum_floor "<<show(slo)
           <<"\npartial_sum_ceil "<<show(shi)<<"\n";
  if(L==32000000){
    assert(-31*scale<slo&&shi<31*scale);
    std::cout<<"strict_full_absolute_upper 100\n";
  }else if(L==64000000){
    assert(1000*slo>85*scale && shi<31*scale);
    std::cout<<"strict_full_interval_zero_to_100\n";
  }
}
