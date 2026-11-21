#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <vector>
using I=std::int64_t;
constexpr I STURM=6912, AP=440;
I mod(I a,I b) { a%=b; return a<0?a+b:a; }
I isqrt(I n) { assert(n>=0); I r=std::sqrt((double)n); while((r+1)*(r+1)<=n) ++r; while(r*r>n) --r; return r; }
std::array<int,23> ch;
std::vector<int> g;
void init(I stop,bool at5) {
    ch.fill(-1); ch[0]=0;
    for(I i=1;i<23;++i) ch[i*i%23]=1;
    g.assign(stop+1,0);
    std::array<std::array<std::vector<I>,253>,2> zmod;
    for(I z=0;z<506;++z) zmod[z%2][15*z*z%253].push_back(z);
    const I Qmax=253*stop, step=at5?5:1;
    for(I u=step;u*u<=Qmax;u+=step) {
      if(u%3==0)continue;
      const int u3=(u%3==1?1:-1);
      for(I y=0;u*u+15*y*y<=Qmax;++y) {
        const I a=u*u+15*y*y, maxz=isqrt((Qmax-a)/15);
        const I b=(10*u+15*y)%23;
        const int wt=u3*ch[b?b:y%23];
        if(!wt)continue;
        for(I z0:zmod[u%2][mod(-a,253)])for(I z=z0;z<=maxz;z+=506) {
          const I n=(a+15*z*z)/253;
          assert((a+15*z*z)%253==0);
          if(!b) assert(z%23==0&&(u-10*y)%23==0);
          if(!at5||n%5==0) g[n]+=wt*(1+(y!=0))*(1+(z!=0));
        }
      }
    }
}
I H(I n) {
  I r=g.at(n);
  for(I k=1;AP*k*k<n;++k)r+=2*g.at(n-AP*k*k);
  return r;
}
struct Box{
  I n=0, nonzero=0, first=0, first_value=0, val8=0;
  std::uint64_t hash=14695981039346656037ULL;
  void put(I i,I x){++n;x=mod(x,16);if(x){++nonzero;if(!first){first=i;first_value=x;}}if(x==8)++val8;hash=(hash^x)*1099511628211ULL;}
  void show(const char* name) const {
    std::cout<<name<<" n "<<n<<" nonzero "<<nonzero<<" value8 "<<val8<<" first "<<first<<" first_value "<<first_value<<" fnv1a "<<hash<<'\n';
  }
};
int main(){
  init(5*STURM,false);
  Box all,guard,guard5;
  for(I n=1;n<=5*STURM;++n){
    I c=g[n], h=H(n);
    if(n<=STURM) all.put(n,h);
    I d=11*n;
    if(n%11!=0&&d%24==17&&ch[d%23]==1){
      assert(c%8==0&&(h-c)%16==0);
      guard.put(n,h);
      if(n%5==0) guard5.put(n,h);
    }
  }
  all.show("H");
  guard.show("guard_n_le_34560");
  guard5.show("guard_plus_5_n_le_34560");
  for(I n:{835,6953,13073,7105}){
    // These are n indices of U11; coefficients of g live at 11*n.
    std::cout<<"sample_d "<<11*n<<" c "<<g[n]<<" H "<<H(n)<<'\n';
  }
  init(5*17*11*STURM,true);
  Box u5,t17u5;
  for(I n=1;n<=STURM;++n){
    u5.put(n,H(5*n));
    // (30/17)=+1, and the integral weight is 2.
    t17u5.put(n,H(5*17*n)+(n%17==0?17*H(5*n/17):0));
  }
  u5.show("U5_H");
  t17u5.show("T17_U5_H");
  Box test;
  for(I n=1;n<=11*STURM;++n){
     I h=n%11?H(85*n)+(n%17==0?17*H(5*n/17):0):0;
     test.put(n,h);
  }
  test.show("drop11_T17_U5_H");
}
