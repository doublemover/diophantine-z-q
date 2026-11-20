
const A=500907037962860804880n, B=204618888056724185n, R=4376874610839020n;
const h=473592745039516333133760n;
const J=15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000n;
const reducedJ=2566827915619116471899843747792873596324159383802094955344492089413795992750334532240167202776488314896151365217289774312203906250n;
const mod=(x,p)=>(x%p+p)%p;
function pow(x,n,p){let z=1n;x=mod(x,p);for(;n;n>>=1n,x=x*x%p)if(n&1n)z=z*x%p;return z}
function inv(x,p){if(mod(x,p)===0n)throw Error("zero inverse");return pow(x,p-2n,p)}
const char=(x,p)=>{const r=pow(x,(p-1n)/2n,p);return r===p-1n?-1n:r};
function sqrt(a,p){
 if(char(a,p)!==1n)return null;
 let d=p-1n,s=0;while(d%2n===0n){d/=2n;s++}
 let n=2n;while(char(n,p)!==-1n)n++;
 let b=pow(a,d,p),g=pow(n,d,p),x=pow(a,(d+1n)/2n,p);
 while(b!==1n){let k=1,r=b*b%p;while(r!==1n){r=r*r%p;k++;if(k>s)throw Error("sqrt")};const z=pow(g,1n<<BigInt(s-k-1),p);x=x*z%p;g=z*z%p;b=b*g%p;s=k}
 if(x*x%p!==a)throw Error("sqrt verification");return x;
}
function gauss(p){if(p%4n===3n)return 0n;const i=sqrt(p-1n,p);for(let g of [i,p-i]){let a=p;while(g*g>p)[a,g]=[g,a%g];const w=BigInt(Math.floor(Math.sqrt(Number(p-g*g))));if(w*w+g*g===p)return w%2n?w:g}throw Error("sum of two squares")}
function curve(p,root){
 const q=(x)=>mod(x,p);
 const cn=(x)=>[q(x),0n], zero=cn(0n), t=root===null?[0n,1n]:cn(root);
 const plus=([a,b],[c,d])=>[q(a+c),q(b+d)], sub=([a,b],[c,d])=>[q(a-c),q(b-d)];
 const mul=([a,b],[c,d])=>[q(a*c+2n*b*d),q(a*d+b*c)];
 const eq=([a,b],[c,d])=>a===c&&b===d;
 const div=(a,[c,d])=>{const n=inv(c*c-2n*d*d,p);return mul(a,[q(c*n),q(-d*n)])};
 const B0=sub(cn(3n),t), D=mul(B0,B0), P=[plus(cn(1n),t),mul(cn(2n),t)];
 function add(U,V){if(!U)return V;if(!V)return U;const [x,y]=U,[u,v]=V;
  if(eq(x,u)&&eq(plus(y,v),zero))return null;
  const m=eq(x,u)?div(sub(mul(cn(3n),mul(x,x)),D),mul(cn(2n),y)):div(sub(v,y),sub(u,x));
  const nx=sub(sub(mul(m,m),x),u);return [nx,sub(mul(m,sub(x,nx)),y)];
 }
 function times(n){let X=null,Y=P;while(n){if(n&1n)X=add(X,Y);n>>=1n;if(n)Y=add(Y,Y)}return X}
 function chart(X){if(!X)return [0,zero];const [x,y]=X, den=plus(mul(x,x),D);if(eq(den,zero))return [-1,zero];
  const f=div(mul(cn(2n),y),den);return [eq(f,zero)?0:1,f];
 }
 function ratio(X,U,V,k){if(U[0]===1&&V[0]>=0)return div(V[1],U[1]);if(U[0]===0&&V[0]===0)return cn(!X||eq(X[0],zero)?k:-k);throw Error("ratio guard")}
 return {times,chart,ratio};
}
function evaluate(pn){
 const p=BigInt(pn), q=(x)=>mod(x,p), r=sqrt(2n,p), c=gauss(p);
 if((A+1n)%p===0n||R%p===0n||char(3n*B,p)!==1n)return {type:"excluded"};
 const order=r===null?p*p+1n-char(7n,p)*(4n*c*c-2n*p):c?(p+1n-2n*c)*(p+1n+2n*c):p+1n;
 const i=pow(6n,15n,order)*pow(3n,65536n,order)%order*(J%order)%order;
 const k=q(pow(6n,15n,p)*pow(3n,65532n,p)*q(reducedJ));
 const sides=(r===null?[r]:[r,p-r]).map(s=>{const e=curve(p,s);if(e.times(order))throw Error("group annihilator check "+p);
  const X=e.times(h%order),U=e.chart(X),V=e.chart(e.times(i));return {e,X,U,V};});
 if(sides.some(o=>o.V[0]<0))throw Error("translated pole below bound");
 const flag=sides.map(o=>o.U[0]===-1);
 if(flag.some(Boolean)){
  if(r===null||p<32407n)throw Error("h pole guard");
  if(flag.every(Boolean))return {type:"pole"};
  const [bad,other]=flag[0]?sides:sides.slice().reverse();
  if(bad.V[0]!==0)throw Error("h pole shifted zero guard");
  return {type:q(R+other.U[1][0]**2n)===0n?"deferred":"pole"};
 }
 const ratios=sides.map(o=>o.e.ratio(o.X,o.U,o.V,k)), uv=sides.map(o=>o.U[1]);
 const norm=([a,b])=>q(a*a-2n*b*b);
 const H=r===null?norm(uv[0]):q(uv[0][0]*uv[1][0]);
 const f=r===null?q(uv[0][0]**2n+2n*uv[0][1]**2n):q((uv[0][0]**2n+uv[1][0]**2n)*inv(2n,p));
 const Q=r===null?norm(ratios[0]):q(ratios[0][0]*ratios[1][0]);
 const N=q(1n+(H*inv(R,p))**2n+2n*f*inv(R,p));
 const qq=q(Q*pow(inv(R,p),15n,p));
 const W=q(N*N+R*qq*qq), cp=q(12n*W*inv(A+1n,p)), D=q(B*cp*cp), F=q(49n*D-48n);
 return {type:"evaluated",formal:sides.some(o=>o.U[0]===0),p:pn,W:Number(W),c:Number(cp),D:Number(D),F:Number(F)};
}
function scan(lower=120000001,upper=10000000000){
 const signs=[[5,1],[7,-1],[11,1],[17,1],[83,1],[131,-1],[163,-1],[661,1],[733,-1],[1489,1],[1861,1],[6551,1],[2470991,1],[16782959,1]];
 const tables=signs.map(([q,s])=>{
   const qr=new Uint8Array(q);
   for(let a=1;a<=Math.floor(q/2);a++)qr[a*a%q]=1;
   return {q,v:s===1?1:0,qr};
 });
 function passes(n,start,end){
   for(let j=start;j<end;j++){
     const {q,v,qr}=tables[j],r=n%q;
     if(!r||qr[r]!==v)return false;
   }
   return true;
 }
 const wheel=157080, residues=[];
 for(let n=1;n<wheel;n+=24)if(passes(n,0,4))residues.push(n);
 const small=new Uint8Array(Math.floor(Math.sqrt(upper))+1), primes=[];
 for(let q=2;q<small.length;q++){
   if(small[q])continue;
   primes.push(q);
   for(let m=q*q;m<small.length;m+=q)small[m]=1;
 }
 function prime(p){
   for(const q of primes){if(q*q>p)return true;if(p%q===0)return false;}
   return true;
 }
 const stats={}, hits=[], formals=[];
 let first, last;
 for(let base=Math.floor(lower/wheel)*wheel;base<=upper;base+=wheel){
   for(const residue of residues){
     const p=base+residue;
     if(p<lower||p>upper||!passes(p,4,tables.length))continue;
     const b=Math.floor((p-1)/1e9)+1;
     const stat=stats[b]??={integers:0,primes:0,evaluated:0,pole:0,deferred:0,excluded:0,hits:0};
     stat.integers++;
     if(!prime(p))continue;
     stat.primes++;
     const r=evaluate(p);
     if(!(r.type in stat))throw Error("unexpected scan status "+r.type);
     stat[r.type]++;
     first??=r;
     last=r;
     if(r.formal)formals.push(r);
     if(r.F===0){stat.hits++;hits.push(r);}
   }
 }
 return {stats,hits,formals,first,last};
}

console.log(JSON.stringify({scan: scan(), control: evaluate(83)}, null, 2));
