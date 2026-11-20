// All-integer independent full direct-height checker. Usage: ./verify height < rows.tsv
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>
using u64 = std::uint64_t;
static constexpr u64 B=204618888056724185ULL;
static constexpr u64 fs[]={5,11,17,163,661,733,1489,1861};
static u64 root(u64 n) {
  u64 lo=0,hi=u64{1}<<32;
  while(hi-lo>1) {
    u64 m=lo+(hi-lo)/2;
    if(m <= n/m) lo=m; else hi=m;
  }
  return lo;
}
static int mod(u64 a,int p) {return a%p;}
struct BaseRow {int p,c;};
struct Row {int p; int allowed; std::vector<unsigned char> lut;};
static Row local(BaseRow r,u64 a,u64 b) {
  const int p=r.p,c=r.c,g=mod(B,p),A=mod(a,p),Bb=mod(b,p);
  std::vector<bool> square(p);
  for(int t=0;t<p;++t) square[t*t%p]=true;
  Row R={p,0,std::vector<unsigned char>(p*p)};
  for(int u=0;u<p;++u) for(int v=0;v<p;++v) if(u||v) {
    const int x=4*u*v%p, y=(A*u*u+Bb*v*v)%p;
    int mask=0;
    for(int sign:{1,-1}) {
      int d=(y+g*c*sign*x)%p, f=(sign*x+c*y)%p;
      int v=(4*d*d-3*g*f*f)%p;
      if(v<0)v+=p;
      if(square[v]) mask|=(sign==1?1:2);
    }
    R.lut[u*p+v]=mask;
    R.allowed+=(mask&1)+(mask>>1);
  }
  return R;
}
int main(int argc,char** argv) {
  if(argc!=2) throw std::runtime_error("height");
  const u64 H=std::stoull(argv[1]); if(!H || H>1000000000000000ULL) throw std::runtime_error("out of range");
  std::vector<BaseRow> rows;
  std::set<int> distinct;
  int p,c;
  while(std::cin>>p>>c) {
    if(p<11||p>241||c<0||c>=p||!distinct.insert(p).second) throw std::runtime_error("bad row");
    for(int k=2;k*k<=p;++k) if(!(p%k)) throw std::runtime_error("nonprime");
    rows.push_back({p,c});
  }
  if(rows.size()!=46 || std::none_of(rows.begin(),rows.end(),[](const auto & r) {return r.p==13 && (4+13*13-3*int(B%13)*r.c*r.c%13)%13==6;}))
    throw std::runtime_error("wrong row carrier");
  std::vector<u64> dvs={1};
  for(u64 q:fs) {
    for(u64 a=2;a<=q/a;++a) if(!(q%a)) throw std::runtime_error("B factor not prime");
    u64 len=dvs.size();
    for(u64 j=0;j<len;++j)dvs.push_back(dvs[j]*q);
  }
  if(dvs.back()!=B||dvs.size()!=256)throw std::runtime_error("wrong B");
  u64 grid=0,mask_after_filters=0,nonprimitive=0,domains=0,survivors=0;
  for(u64 d:dvs) for(u64 e:{1ULL,3ULL}) {
    const u64 a=(B/d)*e,b=(3/e)*d;
    if(a+b>4*H)continue;
    ++domains;
    std::vector<Row> table;
    for(auto r:rows) table.push_back(local(r,a,b));
    std::sort(table.begin(),table.end(),[](const Row & x,const Row & y){
      return u64(x.allowed)*(y.p*y.p-1)<u64(y.allowed)*(x.p*x.p-1);
    });
    const bool swap=a<b;
    const u64 outer=swap?b:a,inner=swap?a:b;
    for(u64 gamma:{1ULL,4ULL}) {
      const u64 cap=gamma*H;
      if(cap<a+b)continue;
      for(u64 z=1,Z=root((cap-inner)/outer);z<=Z;++z) {
        if(gamma==4 && z%2==0)continue;
        const u64 W=root((cap-outer*z*z)/inner);
        for(u64 w=1;w<=W;w+=(gamma==4?2:1)) {
          if(gamma==1 && (z%2 && w%2))continue;
          ++grid;
          const u64 u=swap?w:z,v=swap?z:w;
          int mask=3;
          for(const auto & r:table) {
            mask&=r.lut[(u%r.p)*r.p+v%r.p];
            if(!mask)break;
          }
          if(!mask)continue;
          ++mask_after_filters;
          if(std::gcd(e*u,d*v)!=1 || std::gcd(v,B/d)!=1 || (e==1&&u%3==0)) {
            ++nonprimitive; continue;
          }
          const u64 X=4*u*v/gamma, Y=(a*u*u+b*v*v)/gamma;
          if(!X || Y>H || std::gcd(X,Y)!=1) throw std::runtime_error("reduction");
          ++survivors;
          std::cout<<"survivor X="<<X<<" Y="<<Y<<" signMask="<<mask<<" d="<<d<<" e="<<e<<" u="<<u<<" v="<<v<<"\n";
        }
      }
    }
  }
  std::cout<<"height="<<H<<" domains="<<domains<<" grid="<<grid<<" mask_after_filters="<<mask_after_filters
           <<" nonprimitive="<<nonprimitive<<" survivors="<<survivors<<"\n";
}
