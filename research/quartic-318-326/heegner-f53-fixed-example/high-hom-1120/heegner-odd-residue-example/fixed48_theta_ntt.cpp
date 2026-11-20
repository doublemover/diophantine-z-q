// Exact mod-P convolution for the four theta factors of f_48.
// Coefficients are lifted to Z using the commented Deligne bound, not FFT.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <numeric>
#include <vector>
constexpr int P=998244353, G=3;
int powmod(int a,int n) {
  int r=1; for (;n;n>>=1,a=(int64_t)a*a%P) if (n&1) r=(int64_t)r*a%P; return r;
}
void ntt(std::vector<int>& x,bool inv) {
  int n=x.size();
  for (int i=1,j=0;i<n;i++) {
    int b=n>>1; for (;(j&b);b>>=1) j^=b;
    j^=b; if(i<j) std::swap(x[i],x[j]);
  }
  for(int l=2;l<=n;l*=2) {
    int w0=powmod(G,(P-1)/l); if(inv) w0=powmod(w0,P-2);
    for(int i=0;i<n;i+=l) for(int k=0,w=1;k<l/2;k++,w=(int64_t)w*w0%P) {
      int a=x[i+k], b=(int64_t)x[i+k+l/2]*w%P;
      x[i+k]=a+b<P?a+b:a+b-P; x[i+k+l/2]=a>=b?a-b:a-b+P;
    }
  }
  if(inv) for (int v=powmod(n,P-2);auto &a:x) a=(int64_t)a*v%P;
}
void pairf(std::vector<int>& x,int c,int t,int cap) {
  for(int i=0;c*i*(i+1)<=cap;i++) for(int j=0;;j++) {
    int k=c*i*(i+1)+t*j*j;if(k>cap) break;
    int a=j==0?1:(j%2?-2:2);
    x[k]=(x[k]+a+P)%P;
  }
}
int main(int argc,char**argv) {
  if(argc!=2)return 1;
  int cap; if (std::sscanf(argv[1],"%d",&cap)!=1 || cap<1 || cap>4000000) return 2;
  // P-1 = 2^23*7*17; these tests certify a primitive generator and P prime.
  assert(P-1==(1<<23)*7*17 && powmod(G,P-1)==1);
  for(int q:{2,7,17}) assert(std::gcd(powmod(G,(P-1)/q)-1,P)==1);
  int n=1; while(n<2*cap+1)n*=2;
  std::vector<int>x(n),y(n);
  pairf(x,1,4,cap);pairf(y,3,12,cap);
  ntt(x,false);ntt(y,false);
  for(int i=0;i<n;i++)x[i]=(int64_t)x[i]*y[i]%P;
  ntt(x,true);
  for(int i=0;i<cap;i++){
    int32_t a=x[i]>P/2?x[i]-P:x[i];
    // Deligne |a_m| <= d(m) sqrt(m) <= 2*m < P/2 for these m.
    assert(-2LL*(i+1)<=a&&a<=2LL*(i+1));
    uint32_t u=a; unsigned char b[4]={static_cast<unsigned char>(u),static_cast<unsigned char>(u>>8),static_cast<unsigned char>(u>>16),static_cast<unsigned char>(u>>24)};
    if(std::fwrite(b,1,4,stdout)!=4) return 3;
  }
}
