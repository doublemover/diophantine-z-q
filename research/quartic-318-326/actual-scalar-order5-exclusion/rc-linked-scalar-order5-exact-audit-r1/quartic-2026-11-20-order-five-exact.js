// Node.js 18+. Keep the exact scalar replay sibling beside this script.

const R=4376874610839020n, beta=204618888056724185n, A=17n*144n*beta, h=473592745039516333133760n;
const one=[1n,0n],zero=[0n,0n];
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]];
const sub=(a,b)=>[a[0]-b[0],a[1]-b[1]];
const mul=(a,b)=>[a[0]*b[0]+2n*a[1]*b[1],a[0]*b[1]+a[1]*b[0]];
const scale=(a,s)=>[a[0]*s,a[1]*s];
const conj=([a,b])=>[a,-b];
const eq0=([a,b])=>a===0n&&b===0n;
const div=(a,b)=>{const [N]=mul(b,conj(b)),c=mul(a,conj(b));if(N===0n||c.some(x=>x%N!==0n))throw Error("inexact division");return c.map(x=>x/N)};
const abs=x=>x<0n?-x:x;
const gcd=(x,y)=>{x=abs(x);y=abs(y);while(y)[x,y]=[y,x%y];return x};
function pm(a,b){const c=Array(a.length+b.length-1).fill(zero);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)c[i+j]=add(c[i+j],mul(a[i],b[j]));return c}
function pa(a,b){return Array.from({length:Math.max(a.length,b.length)},(_,i)=>add(a[i]??zero,b[i]??zero))}
function rem(a,g){const b=a.slice(),d=g.length-1;for(let i=b.length-1;i>=d;i--)if(!eq0(b[i]))for(let j=0;j<d;j++)b[i-d+j]=sub(b[i-d+j],mul(g[j],b[i]));return Array.from({length:d},(_,i)=>b[i]??zero)}
function times(a,b,g){return rem(pm(a,b),g)}
function det(m){const v=m.map(r=>r.slice());let old=one,s=1n;for(let k=0;k<m.length-1;k++){if(eq0(v[k][k])){let i=k+1;while(i<m.length&&eq0(v[i][k]))i++;if(i===m.length)return zero;[v[k],v[i]]=[v[i],v[k]];s=-s;}const p=v[k][k];for(let i=k+1;i<m.length;i++)for(let j=k+1;j<m.length;j++)v[i][j]=div(sub(mul(p,v[i][j]),mul(v[i][k],v[k][j])),old);old=p;}return scale(v.at(-1).at(-1),s)}
function algebraNorm(a,g){a=rem(a,g);const n=g.length-1,v=[];for(let i=0;i<n;i++){v.push(a);a=rem([zero,...a],g)}return det(Array.from({length:n},(_,i)=>v.map(c=>c[i])))}
function powMod(a,n,M){let r=1n%M;for(;n;n>>=1n,a=a*a%M)if(n&1n)r=r*a%M;return r}
function make(ell){
 const n=ell===3?4:12,E=BigInt(ell);
 const p3=[-1n,0n,-6n,0n,3n].map(x=>[x,0n]),y2=[0n,-1n,0n,1n].map(x=>[x,0n]),g4=[1n,0n,-5n,0n,-5n,0n,1n].map(x=>[x,0n]);
 const psi=ell===3?p3:pa(pm(pm(y2,y2),g4).map(x=>scale(x,32n)),pm(pm(p3,p3),p3).map(x=>scale(x,-1n)));
 const g=psi.map((v,i)=>i===n?one:scale(v,E**BigInt(n-1-i)));
 if(psi[n][0]!==E)throw Error("leading");
 const D=[E*E,0n,1n],d0=g.map(x=>x[0]),quot=new Array(n-1).fill(0n);
 for(let k=n;k>=2;k--){quot[k-2]=d0[k];d0[k-2]-=D[0]*d0[k];d0[k]=0n;}
 if(d0[1]!==0n||d0[0]===0n)throw Error("denominator inverse");
 const L=7n*R*d0[0]**2n;
 const q=quot.map(x=>[x,0n]), v=rem(pm(pm(q,q),[zero,[-E*E,0n],zero,one]),g);
 const s=v.map(x=>mul([12n*E,4n*E],x));
 s[0]=add(s[0],[L,0n]);
 const s2=times(s,s,g),w=times(s2,s2,g);
 const trace=[BigInt(n)];
 for(let k=1;k<n;k++){let x=BigInt(k)*g[n-k][0];for(let j=1;j<k;j++)x+=g[n-j][0]*trace[k-j];trace.push(-x)}
 const zs=[zero],f=[one];
 let el=[one];
 for(let k=1;k<=n;k++){
  el=times(el,w,g);zs.push(el.reduce((s,x,j)=>add(s,scale(x,trace[j])),zero));
  let coeff=zero;for(let j=1;j<=k;j++)coeff=add(coeff,mul(f[k-j],zs[j]));
  f.push(div(scale(coeff,-1n),[BigInt(k),0n]));
 }
 f.reverse();
 return {L,g,f};
}
function residues(M,ell){
 const mod=x=>(x%M+M)%M, a=(u,v)=>add(u,v).map(mod), b=(u,v)=>sub(u,v).map(mod), p=(u,v)=>mul(u,v).map(mod), c=(u,n)=>scale(u,n).map(mod),sq=u=>p(u,u),cube=u=>p(sq(u),u);
 const X=[1n,1n],Y=[0n,2n],D=[3n,-1n],F=c(sq(D),-1n),X2=sq(X),X4=sq(X2),X6=p(X4,X2),F2=sq(F);
 const p3=b(a(c(X4,3n),c(p(F,X2),6n)),F2);
 const q4=c(b(b(a(X6,c(p(F,X4),5n)),c(p(F2,X2),5n)),p(F,F2)),2n);
 const Y4=sq(sq(c(Y,2n)));
 const seen=new Map([[0n,zero],[1n,one],[2n,one],[3n,p3],[4n,q4]]);
 function q(n){if(seen.has(n))return seen.get(n);const k=n/2n;
  let z;if(n%2n===0n)z=p(q(k),b(p(q(k+2n),sq(q(k-1n))),p(q(k-2n),sq(q(k+1n)))));
  else {const u=p(q(k+2n),cube(q(k))),v=p(q(k-1n),cube(q(k+1n)));z=k%2n?b(u,p(Y4,v)):b(p(Y4,u),v);}
  seen.set(n,z);return z;
 }
 const all=q(BigInt(ell)*h), id=q(h);
 return {all,id,count:seen.size};
}
function solve(ell){
 const {L,g,f}=make(ell),d=g.length-1;
 const fixed=2n*3n*5n*7n*R*(1n+A)*beta;
 const targets=[["H",144n*beta,(A+1n)**2n],["Lprime",7056n*beta,48n*(A+1n)**2n]];
 return targets.map(([name,K,Q])=>{
   const q=Q*L**8n, li=L**4n;
   const prod=Array.from({length:d+1},(_,i)=>scale(conj(f[d-i]),q**BigInt(d-i)*K**BigInt(i)));
   const pair=algebraNorm(prod,f);
   const oneArm=algebraNorm([[-q,0n],[K*li,0n]],f);
   if(pair[1]!==0n)throw Error("pair norm not rational");
   const exact=abs(pair[0]*mul(oneArm,conj(oneArm))[0]);
   if(!exact)throw Error("exact determinant zero");
   const M=exact/gcd(exact,powMod(fixed,BigInt(exact.toString(2).length),exact));
   const {all,id,count}=residues(M,ell);
   const G=gcd(gcd(M,all[0]),all[1]);
   const G0=gcd(gcd(G,id[0]),id[1]);
   const rest=G/gcd(G,powMod(G0,BigInt(G.toString(2).length),G));
   return {name,rawBits:exact.toString(2).length,bits:M.toString(2).length,bothKilled:String(G),bothIdentity:String(G0),nontrivial:String(rest),count,modulus:M.toString(16)};
 });
}

const fs = require("node:fs"), path = require("node:path");
const scalarFile = path.join(__dirname,"quartic-2026-11-20-single-prime-scan.js");
const scalarSource = fs.readFileSync(scalarFile,"utf8").split("function scan(")[0]
  .replace("||char(3n*B,p)!==1n","");
const {evaluate} = new Function(scalarSource+"\nreturn {evaluate}")();
function isPrime(n){if(n<2)return false;for(let k=2;k*k<=n;k++)if(n%k===0)return false;return true;}
const J=15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000n;
const shift=6n**15n*3n**65536n*J;
if(shift%(5n*h)!==0n)throw Error("5 does not divide the translated-index ratio");
const cases=solve(5);
if(cases[0].nontrivial!=="521" || cases[1].nontrivial!==String(89**2*199))throw Error("gcd or factor mismatch");
const local=[521,89,199].map(p=>{
  if(!isPrime(p))throw Error("candidate factor is composite "+p);
  const row=evaluate(p);
  if(row.type!=="evaluated" || (p===521?row.D===1:row.F===0))throw Error("unexcluded candidate "+p);
  return row;
});
console.log(JSON.stringify({result:cases.map(({modulus,...row})=>row),local},null,2));
