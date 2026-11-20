// Save this file beside quartic-2026-11-20-single-prime-scan.js in order
// to rederive the c residues from the actual fixed scalar. Node.js 18+.
// Pass a maximum positive denominator, up to floor(Number.MAX_SAFE_INTEGER/4).
const fs = require("node:fs");
const path = require("node:path");
const expectedRows = [[11,1],[13,8],[17,12],[19,1],[23,1],[31,2],[37,30],[41,18],[43,9],[47,39],[53,45],[59,57],[61,55],[67,53],[71,43],[73,53],[79,1],[83,71],[89,28],[97,46],[101,8],[103,84],[107,48],[109,44],[113,36],[127,96],[131,54],[137,64],[139,125],[149,34],[151,142],[157,117],[167,87],[173,101],[179,59],[191,37],[193,154],[197,66],[199,122],[211,172],[223,91],[227,223],[229,35],[233,95],[239,25],[241,22]];
const sibling = path.join(__dirname,"quartic-2026-11-20-single-prime-scan.js");
function loadRows(){
  if(!fs.existsSync(sibling))return expectedRows.map(([p,c])=>({p,c}));
  const source = fs.readFileSync(sibling,"utf8").split("function scan(")[0]
    .replace("||char(3n*B,p)!==1n","");
  const {evaluate} = new Function(source+"\nreturn {evaluate}")();
  return expectedRows.map(([p,c])=>{
    const actual = evaluate(p);
    if(actual.type!=="evaluated" || actual.c!==c)throw Error("scalar mismatch at "+p);
    return {p,c};
  });
}

const beta=204618888056724185n, factors=[5n,11n,17n,163n,661n,733n,1489n,1861n];
const divisors=factors.reduce((d,p)=>d.concat(d.map(x=>x*p)),[1n]);
const gcd=(a,b)=>{while(b)[a,b]=[b,a%b];return a};
const mod=(x,p)=>(x%p+p)%p;
function maxRoot(n){let x=Math.floor(Math.sqrt(n));while((x+1)**2<=n)x++;while(x*x>n)x--;return x}
function localRows(rows,a,b){
 return rows.map(({p,c})=>{
   const A=Number(a%BigInt(p)),B=Number(b%BigInt(p)), g=Number(beta%BigInt(p));
   const qr=new Uint8Array(p), inv=new Uint16Array(p);
   qr[0]=1;inv[1]=1;
   for(let i=1;i<p;i++){qr[i*i%p]=1;if(i>1)inv[i]=p-Math.floor(p/i)*inv[p%i]%p;}
   function ok(u,v){
     const x=4*u*v%p, y=(A*u*u+B*v*v)%p;
     const plus=(x+c*y)%p, other=(y+g*c*x)%p;
     return qr[mod(4*other*other-3*g*plus*plus,p)];
   }
   const masks=new Uint8Array(p+1);
   for(let t=0;t<p;t++)masks[t]=ok(t,1)+2*ok(mod(-t,p),1);
   masks[p]=3*ok(1,0);
   return {p,inv,masks, weight:masks.reduce((n,v)=>n+(v&1)+(v>>1),0)/(p+1)};
 }).sort((a,b)=>a.weight-b.weight);
}
function bounded(height,rows){
 if(4*height>Number.MAX_SAFE_INTEGER)throw Error("height too large");
 let grid=0, primitive=0, survivors=[], domains=0;
 const cap=BigInt(4*height);
 for(const d of divisors)for(const e of [1n,3n]){
   const a=beta/d*e,b=3n/e*d;
   if(a+b>cap)continue;
   domains++;
   const A=Number(a),B=Number(b),D=Number(d),E=Number(e);
   const table=localRows(rows,a,b);
   const swap=A<B, outer=swap?B:A,inner=swap?A:B;
   for(const gamma of [1,4]){
     const H=gamma*height;
     for(let z=1,Z=maxRoot(Math.floor((H-inner)/outer));z<=Z;z++){
       if(gamma===4 && z%2===0)continue;
       if(!swap && (gcd(z,D)!==1 || E===1&&z%3===0))continue;
       const max=maxRoot(Math.floor((H-outer*z*z)/inner));
       for(let w=1;w<=max;w+=gamma===4?2:1){
         if(gamma===1&&(w&z&1))continue;
         grid++;
         const u=swap?w:z,v=swap?z:w;
         let mask=3;
         for(const {p,inv,masks} of table){
           const U=u%p,V=v%p;
           if(U===0&&V===0){mask=0;break;}
           mask &= masks[V===0?p:U*inv[V]%p];
           if(!mask)break;
         }
         if(!mask)continue;
         if((E===1&&u%3===0)||gcd(E*u,D*v)!==1||gcd(BigInt(v),beta/d)!==1n)continue;
         primitive++;
         const X=4*u*v/gamma,Y=(A*u*u+B*v*v)/gamma;
         survivors.push({X,Y,mask,d:String(d),e:E,u,v});
       }
     }
   }
 }
 return {height,rows:rows.map(r=>r.p),domains,grid,primitive,survivors};
}
console.log(JSON.stringify(bounded(Number(process.argv[2] || 100000000000000),loadRows()),null,2));
