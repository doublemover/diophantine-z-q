
#include <bits/stdc++.h>
using namespace std;
using LL=long long; using W=__int128;
LL mul(LL a,LL b,LL p){return W(a)*b%p;}
LL powm(LL x,LL n,LL p){LL a=1;while(n){if(n&1)a=mul(a,x,p);x=mul(x,x,p);n>>=1;}return a;}
bool chi(LL a,LL p){return powm(a,(p-1)/2,p)==1;}
const LL table[][2]={{415721,330964},{575921,97656},{3162001,1000842},{3641809,3641801},{4247281,283600},{4818481,4818473},{8912209,2815970},{9807649,5794107},{16688017,10016163},{17590513,7707426},{52056721,13280062},{53279089,53279081},{95810641,50406246},{172237889,95970056},{344853841,344853833},{583021393,225544516},{1185793321,867472837},{1476960817,876967193},{32687299769,21523823948}};
int main(int n,char**v){
 LL L=atoll(v[1]);
 for(LL u=1;u<=L;u+=2){
  if(u%3==0||u%17==0)continue;
  bool ok=true;
  for(auto r:table){
    LL p=r[0],x=mul(u%p,u%p,p);
    if(!chi((mul((16*x+r[1])%p,x,p)+1)%p,p)){ok=false;break;}
  }
  if(ok)cout<<u<<"\n";
 }
}
