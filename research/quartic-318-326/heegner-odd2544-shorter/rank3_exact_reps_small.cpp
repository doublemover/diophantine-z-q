// Exact integer search for one bounded rank-three positive definite form.
// The bound inputs are exact Python adjugate computations. No production claim.
#include <array>
#include <cmath>
#include <iostream>
#include <limits>
using i128 = __int128_t;
using I = long long;
int main() {
  I a,b,c,p,q,r,n,X,Y;
  if (!(std::cin >> a >> b >> c >> p >> q >> r >> n >> X >> Y)) return 2;
  if (c <= 0 || n <= 0 || X < 0 || Y < 0 || X > 100000 || Y > 100000) return 3;
  std::array<std::array<I,3>,3> V {};
  for (auto &v : V) for (auto &u : v) {
    if (!(std::cin >> u) || u < -10000 || u > 10000) return 4;
  }
  const I limit=1000000;
  for (I u : {a,b,c,p,q,r}) if (u < -limit || u > limit) return 5;
  for (I x=-X;x<=X;x++) for (I y=-Y;y<=Y;y++) {
    i128 h=i128(q)*x+i128(r)*y;
    i128 delta=h*h+4*i128(c)*(i128(n)-i128(a)*x*x-i128(b)*y*y-i128(p)*x*y);
    if (delta<0) continue;
    // Scope guards above keep delta < 2^100; integer correction is definitive.
    i128 s=(i128)std::sqrt((long double)delta);
    while (s*s>delta) --s;
    while ((s+1)*(s+1)<=delta) ++s;
    if (s*s!=delta) continue;
    for (int k: {1,-1}) {
      if (k<0 && s==0) break;
      i128 z0=k*s-h, m=2*i128(c);
      if (z0%m) continue;
      i128 zz=z0/m;
      if (zz <= -i128(1000000000) || zz >= i128(1000000000)) return 6;
      I z=(I)zz;
      for (int j=0;j<3;j++)
        std::cout << (x*V[0][j]+y*V[1][j]+z*V[2][j]) << (j==2?'\n':' ');
    }
  }
}
