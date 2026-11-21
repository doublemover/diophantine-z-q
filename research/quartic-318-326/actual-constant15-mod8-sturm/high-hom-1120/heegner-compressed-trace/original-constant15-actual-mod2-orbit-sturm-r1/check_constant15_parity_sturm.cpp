// Complete exact mod-2 integral weight-two Sturm test. No production X-index is evaluated.
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
using I=std::int64_t;
constexpr I N=16*15*121;
constexpr I INDEX=(N/2)*3*4/3*6/5*12/11;
static_assert(N==29040&&INDEX==76032);
constexpr I S=INDEX/6, MAX=5*11*17*23*S;
static_assert(S==12672);
bool nonres11(I m) {
  switch(m%11) {
    case 2: case 6: case 7: case 8: case 10:return true;
    default:return false;
  }
}
std::vector<bool> B;
void init() {
  B.assign(MAX/16+1,false);
  // B^-(m) is positive (r,s) norm orbit count modulo two.
  for(I s=1;15*s*s<=4*(MAX/16);++s)
    for(I r=s%2?1:2;r*r+15*s*s<=4*(MAX/16);r+=2) {
      I a=(r*r+15*s*s)/4;
      if(nonres11(a))B[a]=!B[a];
    }
}
bool coeff(I n) {
  bool t=0;
  for(I y=1;15*y*y<=n;y+=2) {
    I m=n-15*y*y;
    if(!(m%16))t^=B[m/16];
  }
  return t;
}
bool U(I n){return coeff(55*n);}
bool T(I n,I p){return U(n*p)^(n%p==0&&U(n/p));}
bool TT(I n){return T(23*n,17)^(n%23==0&&T(n/23,17));}
int main(){
  init();
  std::cout<<"level "<<N<<" index "<<INDEX<<" sturm "<<S<<"\n";
  for(int q=0;q<4;++q) {
    I first=0, ct=0;std::uint64_t hash=14695981039346656037ULL;
    for(I n=1;n<=S;++n) {
      bool z=q==0?U(n):q==1?T(n,17):q==2?T(n,23):TT(n);
      if(z){++ct;if(!first)first=n;}
      hash=(hash^z)*1099511628211ULL;
    }
    const std::array<const char*,4> labels={"U5_U11","T17_U5_U11","T23_U5_U11","T17_T23_U5_U11"};
    if(q>=2)assert(!ct);
    std::cout<<"sturm_prefix "<<labels[q]<<" first "<<first<<" nonzero "<<ct<<" fnv1a "<<hash<<"\n";
  }
}
