#include <bits/stdc++.h>
using namespace std;
using I=long long;
using W=__int128;
vector<int> sp;
I md(I a,I p){a%=p;return a<0?a+p:a;}
I pm(I a,I b,I p){return W(a)*b%p;}
I pw(I x,I k,I p){I a=1;x=md(x,p);for(;k;k>>=1,x=pm(x,x,p))if(k&1)a=pm(a,x,p);return a;}
int le(I x,I p){I y=pw(x,(p-1)/2,p);return y==0?0:y==1?1:-1;}
I ts(I n,I p){assert(le(n,p)==1); I q=p-1,s=0;while(!(q&1))q>>=1,++s;
 I z=2;while(le(z,p)!=-1)++z;
 I c=pw(z,q,p),t=pw(n,q,p),r=pw(n,(q+1)/2,p),m=s;
 while(t!=1){I i=0,u=t;while(u!=1) u=pm(u,u,p),++i;assert(i<m);I b=pw(c,1LL<<(m-i-1),p);r=pm(r,b,p);t=pm(pm(t,b,p),b,p);c=pm(b,b,p);m=i;}
 assert(pm(r,r,p)==md(n,p));return r;
}
pair<I,I> corn(I p) {
 I v=ts(p-1,p);v=min(v,p-v);
 I u=p;
 while(W(v)*v>p){I r=u%v; u=v;v=r;}
 I w=sqrtl(p-v*v);while((w+1)*(w+1)<=p-v*v)++w;while(w*w>p-v*v)--w;
 assert(W(v)*v+W(w)*w==p);return (v&1)?make_pair(v,w):make_pair(w,v);
}
struct P {I x,y;bool inf;};
P add(P X,P Y,I a,I p){
 if(X.inf)return Y;if(Y.inf)return X;
 if(X.x==Y.x && md(X.y+Y.y,p)==0)return {0,0,1};
 I k=X.x==Y.x? pm(md(pm(3*X.x%p,X.x,p)+a,p),pw(2*X.y,p-2,p),p)
 :pm(md(Y.y-X.y,p),pw(Y.x-X.x,p-2,p),p);
 I x=md(pm(k,k,p)-X.x-Y.x,p);
 I y=md(pm(k,X.x-x,p)-X.y,p);
 assert(md(pm(y,y,p)-pm(x,pm(x,x,p)+a,p),p)==0);
 return {x,y,0};
}
P mul(I n,P X,I a,I p){P O{0,0,1};for(;n;n>>=1,X=add(X,X,a,p))if(n&1)O=add(O,X,a,p);return O;}

vector<I> factors(I n) {
 vector<I> f; 
 for (I p=2;1LL*p*p<=n;p+=(p==2?1:2))if(n%p==0){
   f.push_back(p);while(n%p==0)n/=p;}
 if(n>1)f.push_back(n);
 return f;
}
I ord_direct(P R,I g,I a,I p) {
 assert(mul(g,R,a,p).inf);
 I n=g;
 for (I l:factors(g))while(n%l==0&&mul(n/l,R,a,p).inf)n/=l;
 return n;
}

int main(int argc,char**argv){
 I L=stoll(argv[1]);
 const int old[]={3162001,3641809,4247281,52056721,53279089,95810641,17590513,1476960817,4818481,344853841,16688017,583021393,172237889,575921,415721,9807649};
 const int local[]={3,5,7,11,37,2399};
 const int pilot=9807649, M=8*3*5*7*11*37, ex[]={13,17,19,23};
 struct Targets {I p,q;};
 vector<vector<Targets>> tab(1<<20); 
 ifstream f(argv[2]); 
 I q1,A,C,sr,o1,o2,g1,g2,q_a,B,D,root,o3,o4,g3,g4,mask,ext;
 int nt=0;
 while(f>>q1>>A>>C>>sr>>o1>>o2>>g1>>g2>>q_a>>B>>D>>root>>o3>>o4>>g3>>g4>>mask>>ext)
    tab[mask+(ext<<16)].push_back({q1,q_a}),++nt;
 assert(nt>0);
 vector<int> rs;
 for(int r=1;r<M;r+=8) {
  bool ok=true;
  for(int p:local)if(p!=2399&&le(r,p)!=le(pilot,p)){ok=false;break;}
  if(ok)rs.push_back(r);
 }
 int phase=0,prime=0,cl=0;set<pair<I,I>> hits;
 for(I k=0;k<=L;k+=M)for(int r:rs){
  I p=k+r;
  if(p<=76176||p>L)continue;
  if(le(p,2399)!=le(pilot,2399)||le(p,415721)!=1)continue;
  int m=0;
  bool eps=true;
  for(int j=0;j<16;j++){
   int x=le(p,old[j]);if(!x){eps=false;break;} m|=(x<0)<<j;
  }
  if(!eps)continue;
  for(int j=0;j<4;j++)m|=(le(p,ex[j])<0)<<(16+j);
  if(tab[m].empty())continue;
  ++phase;
  if(factors(p)!=vector<I>{p})continue;
  ++prime;
  vector<Targets> targets;
  for(auto a:tab[m])if(le(p,a.p)==1&&le(p,a.q)==1)targets.push_back(a); 
  if(targets.empty())continue;
  auto [A,C]=corn(p);
  I G0=p+1-2*A,G1=p+1+2*A,dg=gcd(G0,G1);
  if(dg&(dg-1))continue;
  if(any_of(old,old+16,[&](int q){return G0%q==0||G1%q==0;}))continue;
  ++cl;
  I sr=ts(2,p);
  I os[2]{},gs[2]{};
  for(int j=0;j<2;j++){
   I v=j?p-sr:sr,a=md(-pm(3-v,3-v,p),p);
   P R{md(1+v,p),2*v%p,0};
   bool z0=mul(G0,R,a,p).inf,z1=mul(G1,R,a,p).inf;
   assert(z0||z1);os[j]=ord_direct(R,z0?(z1?dg:G0):G1,a,p);gs[j]=z0?(z1?0:G0):G1;
  }
  if(gs[0]&&gs[1])assert(gs[0]!=gs[1]);
  for(int j=0;j<2;j++)if(os[1-j]%2&&gcd(os[0],os[1])==1){
   for(auto x:targets)if(G0%x.p&&G1%x.p&&G0%x.q&&G1%x.q)
    cout<<x.q<<","<<x.p<<","<<p<<","<<A<<","<<C<<","<<(j?p-sr:sr)<<","<<os[j]<<","<<os[1-j]<<","<<G0<<","<<G1<<"\n";
  }
 }
 cerr<<"mate restrictions="<<nt<<" wheel residues="<<rs.size()<<" full phase="<<phase<<" prime="<<prime<<" count plus cross="<<cl<<"\n";
}
