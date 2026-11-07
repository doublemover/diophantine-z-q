'use strict';
// Independent reconstruction of the public Brox v3 arithmetic system.
// No author gate program or coefficient table is imported.
const fs=require('node:fs'), path=require('node:path'), crypto=require('node:crypto');
const OUT=__dirname;
function abs(a){return a<0n?-a:a;}
function gcd(a,b){a=abs(a);b=abs(b);while(b){let c=a%b;a=b;b=c;}return a;}
function Q(n,d=1n){n=BigInt(n);d=BigInt(d);if(!d)throw Error('zero rational denominator');if(d<0n){n=-n;d=-d;}let g=gcd(n,d);return[n/g,d/g];}
const qadd=(a,b)=>Q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
const qmul=(a,b)=>Q(a[0]*b[0],a[1]*b[1]);
const qneg=a=>[-a[0],a[1]], qinv=a=>Q(a[1],a[0]);
const qstr=a=>`${a[0]}/${a[1]}`;
const key=(m,s=0)=>s+'|'+m.join(',');
function unpack(k){let [s,m]=k.split('|');return[Number(s),m?m.split(',').map(Number):[]];}
function term(c,m=[],s=0){c=Array.isArray(c)?c:Q(c);return c[0]?new Map([[key(m,s),c]]):new Map();}
const C=(n,d=1)=>term(Q(n,d)), zero=C(0), one=C(1);
function add(...ps){let r=new Map();for(let p of ps)for(let[k,c]of p){let v=qadd(r.get(k)||Q(0),c);if(v[0])r.set(k,v);else r.delete(k);}return r;}
function scale(p,c){c=Array.isArray(c)?c:Q(c);return new Map([...p].map(([k,a])=>[k,qmul(a,c)]).filter(([,a])=>a[0]));}
const sub=(a,b)=>add(a,scale(b,-1));
function mul(a,b){let r=new Map();for(let[k,c]of a)for(let[l,d]of b){let[sk,m]=unpack(k),[sl,n]=unpack(l);let z=key([...m,...n].sort((x,y)=>x-y),sk+sl);let v=qadd(r.get(z)||Q(0),qmul(c,d));if(v[0])r.set(z,v);else r.delete(z);}return r;}
const sq=a=>mul(a,a);
function degree(p){return Math.max(0,...[...p.keys()].map(k=>unpack(k)[1].length));}
function encode(p){return[...p].sort(([a],[b])=>a.localeCompare(b)).map(([k,c])=>{let[s,m]=unpack(k);return{monomial:m,sPower:s,coefficient:qstr(c)};});}
function signature(p){return JSON.stringify(encode(p));}
function constant(p){if(!p.size)return Q(0);if(p.size!==1||!p.has('0|'))return null;return p.get('0|');}
let coords=[],residuals=[],gates=[],values={},guards=[],cse=new Map(),divisionCse=new Map(),census=[];
let block='base', src=[2354,2487];
function fresh(name,kind='gate',protect=false){let id=coords.length;coords.push({id,name,kind,protected:protect,block,sourceLines:src});return term(1,[id]);}
function idof(p){let t=[...p];if(t.length!==1)throw Error('not variable');let[s,m]=unpack(t[0][0]);if(s||m.length!==1||qstr(t[0][1])!=='1/1')throw Error('not variable');return m[0];}
function residual(name,p,kind='structural'){if(degree(p)>2)throw Error(`${name} has degree ${degree(p)}`);let id=residuals.length;residuals.push({id,name,kind,block,sourceLines:src,terms:encode(p)});return id;}
function deps(...ps){return[...new Set(ps.flatMap(p=>[...p.keys()].flatMap(k=>unpack(k)[1])))].sort((a,b)=>a-b);}
function save(name,p){values[name]={terms:encode(p),block,sourceLines:src};return p;}
function saveF(name,a){save(name+'.0',a[0]);save(name+'.1',a[1]);return a;}
function assign(name,p){
 if(degree(p)>2)throw Error(`${name} assignment degree ${degree(p)}`);
 if(degree(p)<=1)return save(name,p);
 let h=new Map(),l=new Map();for(let[k,c]of p)(unpack(k)[1].length===2?h:l).set(k,c);
 let lead=[...h].sort(([a],[b])=>a.localeCompare(b))[0][1], norm=scale(h,qinv(lead)), sig=signature(norm), v=cse.get(sig);
 if(!v){v=fresh(name+'.quadratic');let ri=residual(name+'.definition',sub(v,norm),'gate');gates.push({coordinateId:idof(v),definitionResidualId:ri,operation:'quadratic_assignment',expression:encode(norm),dependencies:deps(norm),block,sourceLines:src});cse.set(sig,v);}
 return save(name,add(scale(v,lead),l));
}
const rm=(name,a,b)=>assign(name,mul(a,b));
const rsq=(name,a)=>assign(name,sq(a));
function rp(name,a,n){if(n===0)return one;if(n===1)return a;let v=rp(name+'.half',a,Math.floor(n/2));v=rsq(name+'.square',v);return n%2?rm(name+'.odd',v,a):v;}
function rquot(name,a,b,domain){
 let bc=constant(b);if(bc){if(!bc[0])throw Error('division by constant zero');return assign(name,scale(a,qinv(bc)));}
 if(degree(b)>1||degree(a)>2)throw Error('quotient degree');
 let sig='Q:'+signature(a)+'/'+signature(b),old=divisionCse.get(sig);if(old)return save(name,old);
 let v=fresh(name);let ri=residual(name+'.definition',sub(mul(b,v),a),'gate');gates.push({coordinateId:idof(v),definitionResidualId:ri,operation:'rational_quotient',numerator:encode(a),denominator:encode(b),domain,dependencies:deps(a,b),block,sourceLines:src});divisionCse.set(sig,v);return save(name,v);
}
// A conditional quotient is a free witness with a structural row.
// Its zero-denominator branch is handled by the t=1 trivial-height lemma.
function witnessQuot(name,a,b){
 const v=fresh(name,'base');residual(name+'.definition',sub(mul(b,v),a));return save(name,v);
}
function inv(name,a){let v=rquot(name,one,a,'equation_enforces_nonzero');guards.push({name,expression:encode(a),inverse:encode(v),sourceLines:src});return v;}
const F=(a,b=0)=>[Array.isArray(a)&&a[0] instanceof Map?a[0]:a instanceof Map?a:C(a),b instanceof Map?b:C(b)];
const fadd=(a,b)=>[add(a[0],b[0]),add(a[1],b[1])], fsub=(a,b)=>[sub(a[0],b[0]),sub(a[1],b[1])];
const fconj=a=>[a[0],scale(a[1],-1)];
const fc=(a,b=0)=>[Array.isArray(a)?term(a):C(a),Array.isArray(b)?term(b):C(b)];
const fscale=(a,c)=>[scale(a[0],c),scale(a[1],c)];
const rawFmul=(a,b)=>[add(mul(a[0],b[0]),scale(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0]))];
function fmul(name,a,b){return saveF(name,[assign(name+'.0',add(mul(a[0],b[0]),scale(mul(a[1],b[1]),2))),assign(name+'.1',add(mul(a[0],b[1]),mul(a[1],b[0])))]);}
function fsq(name,a){return fmul(name,a,a);}
function fscalar(name,a,b){return saveF(name,[rm(name+'.0',a[0],b),rm(name+'.1',a[1],b)]);}
function fquot(name,a,b,domain){
 let b0=constant(b[0]),b1=constant(b[1]);
 if(b0&&b1){let norm=qadd(qmul(b0,b0),qneg(qmul(Q(2),qmul(b1,b1))));if(!norm[0])throw Error('field constant denominator zero');return fmul(name,a,[term(qmul(b0,qinv(norm))),term(qneg(qmul(b1,qinv(norm))))]);}
 let sig='FQ:'+signature(a[0])+','+signature(a[1])+'/'+signature(b[0])+','+signature(b[1]);let old=divisionCse.get(sig);if(old)return saveF(name,old);
 let z=[fresh(name+'.0'),fresh(name+'.1')];
 let eqs=[sub(add(mul(b[0],z[0]),scale(mul(b[1],z[1]),2)),a[0]),sub(add(mul(b[0],z[1]),mul(b[1],z[0])),a[1])];
 for(let j=0;j<2;j++){let ri=residual(name+'.definition.'+j,eqs[j],'gate');gates.push({coordinateId:idof(z[j]),definitionResidualId:ri,operation:'field_quotient_component',component:j,numerator:a.map(encode),denominator:b.map(encode),output:z.map(encode),domain,dependencies:deps(...a,...b),block,sourceLines:src});}
 divisionCse.set(sig,z);return saveF(name,z);
}
function finv(name,a){let z=fquot(name,fc(1),a,'equations_enforce_nonzero');guards.push({name,fieldExpression:a.map(encode),fieldInverse:z.map(encode),sourceLines:src});return z;}
function start(name,lines){block=name;src=lines;census.push({block,startCoordinates:coords.length,startResiduals:residuals.length});}
// Allocate the displayed 90 base coordinates before arithmetic gates.
const X=fresh('input','input',true), names=['UA','US','UT','UZ','VA','VS','VT','VZ'];
let half={};for(let n of names)half[n]={x:[fresh(n+'.chart.h0','base'),fresh(n+'.chart.h1','base')],y:[fresh(n+'.chart.j0','base'),fresh(n+'.chart.j1','base')]};
const anchorFH=[fresh('H.freeF.0','base'),fresh('H.freeF.1','base')],anchorW=[fresh('fixedAnchor.w.0','base'),fresh('fixedAnchor.w.1','base')],anchorNormRoot=fresh('H.normRoot','base');
const lambda=fresh('lambda','base');
let poles=[];for(let r=0;r<3;r++)poles.push({e:fresh('detector'+r+'.scaled_e','base'),s:fresh('detector'+r+'.s','base'),p:fresh('detector'+r+'.p','base'),q:fresh('detector'+r+'.q','base')});
const scalar={e:fresh('scalar.scaled_e','base'),s:fresh('scalar.s','base'),p:fresh('scalar.p','base'),q:fresh('scalar.q','base')};
const anchor=[fresh('anchor.u','base',true),fresh('anchor.v','base',true),fresh('anchor.w','base',true)];
const booleans=[];
if(coords.length!==58)throw Error('base count '+coords.length);

const D=fc(11,-6), P={x:fc(Q(57,8),Q(-7,2)),y:fc(Q(-165,8),Q(417,32)),h:fc(-1,Q(7,4)),j:fc(Q(39,8),Q(-9,2))};
function double(name,Qp,withCurve=false){
 if(withCurve)throw Error('new double expects the already certified square-abscissa chart');
 const k=fquot(name+'.k',fadd(rawFmul(Qp.x,Qp.x),D),fscale(Qp.j,2),'nonzero_j_on_square_abscissa_chart');
 const h=fquot(name+'.h',k,Qp.h,'nonzero_h_on_square_abscissa_chart');
 const x=fsq(name+'.xSquare',h);
 const u=fquot(name+'.tSquare',rawFmul(Qp.j,Qp.j),fscale(Qp.x,2),'nonzero_x_on_square_abscissa_chart');
 const j=fsub(u,x),y=rawFmul(h,j);
 return {h:saveF(name+'.h',h),j:saveF(name+'.j',j),x:saveF(name+'.x',x),y:saveF(name+'.y',y)};
}
start('point_modules',[4311,4348]);
let points={};for(let n of names){
 const u=half[n].x,v=half[n].y,f=fsq(n+'.reciprocal.f',u);
 const relation=fsub(fadd(rawFmul(v,v),rawFmul(D,rawFmul(f,f))),fc(1));
 for(let j=0;j<2;j++)residual(n+'.reciprocal.equation.'+j,relation[j]);
 points[n]={u,v,f,reciprocal:true};
}
const fixedK=P.h,fixedM=P.j,fixedK2=P.x;
start('fixed_anchor',[2394,2399]);
{
 const fH=saveF('H.freeF',anchorFH),t=fmul('fixedAnchor.t',fH,anchorW),fV=fmul('V0.reciprocal.f',t,anchorW);
 const relation=fsub(fsub(fsub(fc(1),rawFmul(fixedK2,fadd(fH,fV))),fscale(rawFmul(fixedM,t),2)),rawFmul(D,rawFmul(t,t)));
 for(let j=0;j<2;j++)residual('fixedAnchor.quarticRelation.'+j,relation[j]);
 const denH=fadd(fadd(fixedM,rawFmul(D,t)),rawFmul(fixedK2,anchorW));
 const denV=fadd(fadd(rawFmul(fixedM,anchorW),rawFmul(D,fV)),fixedK2);
 residual('H.normSquareRootEquation',sub(sq(anchorNormRoot),sub(sq(fH[0]),scale(sq(fH[1]),2))));
 points.H={f:fH,compressedAnchor:'H',logDenominator:denH};
 points.V0={f:fV,compressedAnchor:'V0',logDenominator:denV};
}
start('reversed_roots',[2394,2399]);
function subtractAbscissa(name,U,V){
 const denominator=fsub(V.f,U.f);
 inv(name+'.realDifferenceInverse',denominator[0]);
 const numerator=fadd(rawFmul(U.u,V.v),rawFmul(V.u,U.v));
 const h=fquot(name+'.squareRoot',numerator,denominator,'retained_nonzero_real_difference_guard');
 return {h};
}
const U=[points.H,points.UA,points.US,points.UT,points.UZ],V=[points.V0,points.VA,points.VS,points.VT,points.VZ];
for(let i=1;i<=4;i++){const name=['','A','S','T','Z'][i];points[name]=subtractAbscissa('root'+name,U[i],V[i]);}
start('parameters_and_logarithms',[2401,2411]);
function parameters(name,p){return {point:p,f:p.f,z:null};}
const PU=U.map((p,i)=>parameters('U'+i,p)),PV=V.map((p,i)=>parameters('V'+i,p));
function finishLog(name,p,out){
 if(p.point.compressedAnchor==='V0')return fquot(name,rawFmul(fixedK,rawFmul(anchorW,out)),p.point.logDenominator,'compressed_anchor_V0_regular_including_identity');
 // The order-one test v-1 forces the +1 local branch; this polynomial numerator is fused into LP.
 return saveF(name+'.directNumerator',fscale(rawFmul(p.point.u,out),-1));
}
const gCoeffs=[Q(1),Q(-2,5)];for(let j=2;j<=4;j++)gCoeffs.push(qmul(gCoeffs[j-1],Q(4*j-5,4*j+1)));
// J(delta)=H(-2delta-delta^2), truncated to the displayed degree.
const hCoeffs=[Q(1),Q(-1,5),Q(1,15),Q(-1,39),Q(7,663)];
// Field polynomial helpers for the degree-nine block circuit.

function rawPolynomial6(coeff,basis){
 let out=fc(0);
 for(let k=0;k<coeff.length;k++){
  let term=k<=3?basis[k]:rawFmul(basis[3],basis[k-3]);
  out=fadd(out,fscale(term,coeff[k]));
 }
 return out;
}
function log(name,p,e){
 const aCoeffs=p.point.compressedAnchor==='V0'?gCoeffs:hCoeffs;
 let w;if(p.point.compressedAnchor==='V0')w=fmul(name+'.w',D,fsq(name+'.fSquare',p.f));
 else {w=saveF(name+'.delta',fsub(p.point.v,fc(1)));p.branchLeaf=w;}
 if(e===13){
  // Pade(2,1): local error order4, hence precision16. Its denominator
  // is nonzero on the actual curve domain, as proved separately.
  const pp=p.point.compressedAnchor==='V0'?[Q(1),Q(-61,65),Q(16,195)]:[Q(1),Q(12,65),Q(-2,195)];
  const qq=p.point.compressedAnchor==='V0'?[Q(1),Q(-7,13)]:[Q(1),Q(5,13)];
  const powers=[fc(1),w,rawFmul(w,w)];
  let num=fc(0),den=fc(0);
  for(let k=0;k<3;k++)num=fadd(num,fscale(powers[k],pp[k]));
  for(let k=0;k<2;k++)den=fadd(den,fscale(powers[k],qq[k]));
  const out=fquot(name+'.polynomial',num,den,'Pade21_denominator_nonzero_on_actual_curve_domain');
  return finishLog(name,p,out);
 }
 const out=saveF(name+'.polynomial',fadd(fc(aCoeffs[0]),fscale(w,aCoeffs[1])));
 return finishLog(name,p,out);
}
const LV=PV.map((p,i)=>log('logV'+i,p,i===1?4:13));
let L=[],LP=[];for(let i=1;i<=4;i++){
 L[i]=fquot('L'+i,rawFmul(U[i].u,points.H.logDenominator),rawFmul(fixedK,U[i].v),'primary_z_ratio_fused_compressed_H');
 LP[i]=fconj(fquot('LP'+i,LV[i],LV[0],'ratio_equations_with_identity_branch_proved_sound'));
}
start('direct_tests_and_shared_symmetric_coefficients',[4575,4605]);
// Odd-square bridge: beta is an odd integer iff X is an integer.
const inputOdd=save('inputOdd',add(scale(X,2),one));
const beta=save('beta',scale(rsq('inputOddSquare',inputOdd),3723));
const CC=fmul('Lucas.C',fsub(L[2],fc(2)),L[4]), AT=fmul('Lucas.AT',L[2],L[3]);
const FF=[assign('Lucas.F0',add(sq(L[3][0]),scale(sq(L[3][1]),2),scale(mul(AT[0],CC[0]),-1),scale(mul(AT[1],CC[1]),-2),sq(CC[0]),scale(sq(CC[1]),2),C(-1))),assign('Lucas.F1',add(scale(mul(L[3][0],L[3][1]),2),scale(mul(AT[0],CC[1]),-1),scale(mul(AT[1],CC[0]),-1),scale(mul(CC[0],CC[1]),2)))];
const v0SquareForNorm=fsq('normV0.fieldSquare',PV[0].f);
const normV0Test=save('normV0.test',sub(sq(PV[0].f[0]),scale(sq(PV[0].f[1]),2)));
const normV0TestSquare=assign('normV0.testSquare',sub(sq(v0SquareForNorm[0]),scale(sq(v0SquareForNorm[1]),2)));
const tests=[...PU.map((p,i)=>({value:i===0?F(anchorNormRoot):p.point.u,order:i===0?4:1})),...PV.map((p,i)=>i===0?({value:F(normV0Test),order:1,square:F(normV0TestSquare)}):({value:fconj(fsub(p.point.v,fc(1))),order:1,parityLeaf:fconj(p.branchLeaf)}))];
for(let i=1;i<=4;i++)tests.push({value:fsub(L[i],LP[i]),order:i===1?4:13});
tests.push({value:fsub(L[1],[beta,zero]),order:4},{value:FF,order:13});
tests.forEach((t,j)=>saveF('test'+j,t.value));
function polyProduct(name, ys) {
 if(ys.length===1)return [fc(1),ys[0]];
 let cut=Math.floor(ys.length/2),a=polyProduct(name+'.left',ys.slice(0,cut)),b=polyProduct(name+'.right',ys.slice(cut)),out=[fc(1)];
 for(let k=1;k<a.length+b.length-1;k++){
  let c=[zero,zero];
  for(let i=Math.max(0,k-b.length+1);i<=Math.min(k,a.length-1);i++){
   let u=a[i],v=b[k-i];
   c[0]=add(c[0],mul(u[0],v[0]),scale(mul(u[1],v[1]),2));
   c[1]=add(c[1],mul(u[0],v[1]),mul(u[1],v[0]));
  }
  out[k]=[assign(name+'.co'+k+'.0',c[0]),assign(name+'.co'+k+'.1',c[1])];
 }
 return out;
}
// The four reciprocal delta leaves have even valuation at every good place.
// They are deliberately NOT squares; the generalized parity chain proves them.
let normLeaves=tests.map((t,j)=>({order:t.order,value:t.parityLeaf?saveF('parityLeaf.'+j,t.parityLeaf):(t.square?saveF('testSquare.'+j,t.square):fsq('testSquare.'+j,t.value))}));
const chainLeaves=[normLeaves[0],normLeaves[5],...normLeaves.slice(1,5),...normLeaves.slice(6)];
start('fixed_height_scales',[3352,3405]);
let productH=fc(1);
for(let n of ['A','S','T','Z'])productH=fmul('heightRootProduct.'+n,productH,points[n].h);
saveF('heightRootProduct',productH);
const productNorm=assign('heightRootProduct.norm',sub(sq(productH[0]),scale(sq(productH[1]),2)));
const shiftedProductTrace=add(productH[0],productNorm);
const scales=[one,save('heightRootProduct.shiftedTraceSquare',sq(shiftedProductTrace)),save('heightRootProduct.normSquare',sq(productNorm))];
const commonMu=inv('commonLambdaInverse',lambda);
// Algebraic abbreviations for the weights: e=(A*delta)^5/F,
// R=1/(e*delta), q1=e/delta^3, q16=q1*e^30, q52=q1*e^102.
function evalSym(name,co,q){
 const n=co.length-1;
 if(n===2){const q2=rsq(name+'.power2',q);return saveF(name,[0,1].map(j=>assign(name+'.sum.'+j,add(co[0][j],mul(co[1][j],q),mul(co[2][j],q2)))));}
 const split=n===9?5:n===7?4:n===5?3:null;
 if(split===null)throw Error('Unexpected grouped detector degree '+n);
 const powers=[one,q];for(let k=2;k<=split;k++)powers[k]=rm(name+'.power'+k,powers[Math.floor(k/2)],powers[Math.ceil(k/2)]);
 const high=[zero,zero];
 for(let k=split;k<=n;k++)for(let j=0;j<2;j++)high[j]=add(high[j],mul(co[k][j],powers[k-split]));
 const block=[assign(name+'.high.0',high[0]),assign(name+'.high.1',high[1])];
 const out=[mul(powers[split],block[0]),mul(powers[split],block[1])];
 for(let k=0;k<split;k++)for(let j=0;j<2;j++)out[j]=add(out[j],mul(co[k][j],powers[k]));
 return saveF(name,[assign(name+'.sum.0',out[0]),assign(name+'.sum.1',out[1])]);
}
function pole(name,b,p,prep){
 if(prep){
  // Preparation-zero predicate. This is a source arithmetic refinement,
  // not a bijection of arbitrary old prepared witnesses.
  // For integer inputs b has square reduced denominator, the required
  // 2/3/17 classes and 0<b<17. For rational inputs nonzero follows from Q2.
  const W=assign(name+'.zeroW',mul(p.e,sub(C(17),b)));
  const V=rsq(name+'.scaledS2',p.s);
  const T=assign(name+'.scaledProduct',mul(sub(V,W),add(V,scale(W,3))));
  residual(name+'.firstConic',add(scale(sq(p.p),17),scale(b,-289),scale(p.e,-578),scale(W,34),scale(sq(p.e),51),scale(mul(p.e,W),-3)));
  residual(name+'.secondConic',sub(scale(sq(p.q),17),mul(b,T)));
  return;
 }
 // Exact existential normalization: old(p,e,s,q)=b*new(p,e,s,q).
 // At b=0 the normalized witness e=17,p=s=q=0 supplies the reverse lift.
 // P=b*p in the previous normalized chart. The zero-b branch has
 // explicit witnesses in both existential gadgets; it is not a bijection there.
 const H=rm(name+'.normalizedH',p.e,sub(C(17),b)),ss=rsq(name+'.normalizedS2',p.s);
 residual(name+'.firstConic',add(scale(sq(p.p),17),scale(b,-289),scale(p.e,-578),scale(H,34),scale(sq(p.e),51),scale(mul(p.e,H),-3)));
 const T=assign(name+'.normalizedProduct',mul(sub(ss,H),add(ss,scale(H,3))));
 residual(name+'.secondConic',sub(scale(sq(p.q),17),mul(b,T)));
}
function chainAssign(name,p){
 if(!p.size)return save(name,p);
 if(degree(p)>2)throw Error('chain assignment degree');
 const v=fresh(name+'.atomic');const ri=residual(name+'.definition',sub(v,p),'gate');
 gates.push({coordinateId:idof(v),definitionResidualId:ri,operation:'quadratic_assignment',expression:encode(p),dependencies:deps(p),block,sourceLines:src});
 return save(name,v);
}
for(let r=0;r<3;r++){
 start('detector_'+r,[2424,2460]);let A=scales[r],t=r===0?rm('detector0.t',A,lambda):rquot('detector'+r+'.t',A,commonMu,'global_inverse_forces_nonzero_mu'),delta=sub(t,one);
 let roots=[Q(0),Q(1,2),Q(1),Q(-1,2399),Q(32,407)],cs=[Q(1)];
 for(let root of roots){let nx=Array(cs.length+1).fill(null).map(()=>Q(0));for(let k=0;k<cs.length;k++){nx[k]=qadd(nx[k],qmul(root,cs[k]));nx[k+1]=qadd(nx[k+1],cs[k]);}cs=nx;}
 let t2=rsq('detector'+r+'.Fsquare',t),middle=assign('detector'+r+'.Fmiddle',add(mul(t2,add(t,term(cs[4]))),scale(t,cs[3]),term(cs[2]))),Fv=assign('detector'+r+'.F',add(mul(t2,middle),scale(t,cs[1]),term(cs[0])));
 let Ad=r===0?rm('detector0.Adelta',A,delta):rm('detector'+r+'.Adelta',commonMu,sub(t2,t));
 let ep,delta2,delta3,q1;
 if(r===0){
  delta2=rsq('detector0.delta2',delta);delta3=rm('detector0.delta3',delta2,delta);
  q1=rquot('detector0.q1',delta2,Fv,'e_inverse_and_assignment_force_delta_and_F_nonzero');
  ep=rm('detector0.eWeight',q1,delta3);
 }else{
  ep=rquot('detector'+r+'.eWeight',mul(rp('detector'+r+'.Adelta4',Ad,4),Ad),Fv,'positive_scale_and_norm_equation_make_numerator_nonzero');
  delta2=rsq('detector'+r+'.delta2',delta);delta3=rm('detector'+r+'.delta3',delta2,delta);q1=witnessQuot('detector'+r+'.q1',ep,delta3);
 }
 const eDelta=rm('detector'+r+'.eDelta',ep,delta);
 const ea=rsq('detector'+r+'.e2',ep);
 const ec=witnessQuot('detector'+r+'.e4OverDelta',sq(ea),delta),q4=witnessQuot('detector'+r+'.q4',sq(ec),eDelta);
 const qa=witnessQuot('detector'+r+'.q7',sq(q4),q1),qb=witnessQuot('detector'+r+'.q13',sq(qa),q1);
 // Left-deep norm chain with shared square or parity-even reciprocal leaves.
 let w=fc(1);const weights={1:q1,4:q4,13:qb};
 for(let j=0;j<chainLeaves.length;j++){const leaf=chainLeaves[j],ww=rawFmul(w,w);w=saveF('detector'+r+'.normChain.'+j,[0,1].map(k=>chainAssign('detector'+r+'.normChain.'+j+'.'+k,add(ww[k],mul(weights[leaf.order],leaf.value[k])))));}
 saveF('detector'+r+'.W',w);
 // Optional trace numerator is a free witness constrained by a quadratic row.
 // Its zero-denominator branch is sound because it has no consumed contacts.
 let nw=fresh('detector'+r+'.normOver2w0','base');
 residual('detector'+r+'.normOver2w0.definition',sub(mul(w[0],nw),scale(sub(sq(w[0]),scale(sq(w[1]),2)),Q(1,2))));save('detector'+r+'.normOver2w0',nw);
 let bv=witnessQuot('detector'+r+'.B',sq(nw),eDelta);
 save('detector'+r+'.Bsemantic',bv);pole('detector'+r,bv,poles[r],false);
}
start('scalar_block',[2462,2489]);
// Same local squareclass11, enlarged by the square(2*3*17)^2.
let correction=C(114444);
let r1=rm('scalar.rPair1',sub(beta,one),sub(beta,C(2401))),r2=rm('scalar.rPair2',add(scale(beta,32),C(343)),sub(scale(beta,2),one)),rr=rm('scalar.r',r1,r2);
let ri=inv('scalar.rInverse',rr),ri16=rp('scalar.rInverse16',ri,16);
// Square-root Kummer entry: R has abscissa x(S-P) or x(S+P).
// Its scalar height proof uses c=|a+-1| and ||a|-c|<=1.
const scalarRRoot=[fresh('scalar.shiftedS.squareRoot.0','base'),fresh('scalar.shiftedS.squareRoot.1','base')];
saveF('scalar.shiftedS.squareRoot',scalarRRoot);
const scalarRootProduct=fmul('scalar.shiftedS.rootProduct',points.S.h,scalarRRoot);
const scalarKummerEquation=fsub(fsub(fsub(rawFmul(scalarRootProduct,scalarRootProduct),rawFmul(P.x,rawFmul(scalarRRoot,scalarRRoot))),fscale(rawFmul(P.j,scalarRootProduct),2)),fadd(rawFmul(P.x,rawFmul(points.S.h,points.S.h)),D));
for(let j=0;j<2;j++)residual('scalar.shiftedS.kummerEquation.'+j,scalarKummerEquation[j]);
const scalarRootNormR=assign('scalar.rootNormR',sub(sq(scalarRRoot[0]),scale(sq(scalarRRoot[1]),2)));
const scalarNormUR=inv('scalar.normUR',scalarRootNormR);
const scalarNormUH=save('scalar.normUH',anchorNormRoot);
const scalarScaledNormH=rquot('scalar.scaledNormUH',scalarNormUH,rr,'retained_scalar_r_inverse');
const scalarNormRatio=rquot('scalar.normalizedNormRatio',mul(scalarNormUR,ri16),scalarScaledNormH,'nonzero_scaled_norm_of_uH');
const scalarPackedNormH=assign('scalar.packedNormH',add(one,sq(scalarScaledNormH),scale(mul(PU[0].f[0],ri),2)));
const scalarQSquare=rsq('scalar.normRatioSquare',scalarNormRatio);
const nw=save('scalar.W',add(sq(scalarPackedNormH),mul(rr,scalarQSquare)));
const scalarCorrectedR=save('scalar.correctedR',scale(rr,114444));
const normalizedW=rquot('scalar.normalizedW',nw,add(one,scalarCorrectedR),'Q2_nonsquare_minus11r_excludes_zero_normalizer');
const bs=rquot('scalar.b',scale(sq(normalizedW),114444),ri,'retained_r_inverse');
pole('scalar',bs,scalar,true);
start('anchor',[4160,4178]);
let fa=save('anchor.physicalA',add(scalarNormUR,mul(term(4096,[],1),productNorm)));
const anchorRow=residual('anchor.equation',add(sq(anchor[0]),scale(sq(anchor[1]),6),scale(sq(anchor[2]),-2),scale(sq(fa),-3),term(2,[],2)));
save('anchor.physicalA',fa);
for(let i=0;i<census.length;i++){let c=census[i],next=census[i+1];c.newCoordinates=(next?next.startCoordinates:coords.length)-c.startCoordinates;c.newResiduals=(next?next.startResiduals:residuals.length)-c.startResiduals;}
const sourceName='sources/diophantine_optimization_20261106_v3.tex';
const inputSource=path.resolve(__dirname,'sources/diophantine_optimization_20261106_v3.tex');
const data={format:'brox-independent-quadratic-ir-v1',source:{path:sourceName,sha256:crypto.createHash('sha256').update(fs.readFileSync(inputSource)).digest('hex'),reconstruction:'independent_from_displayed_formulas_not_original_gate_bytes',refinements:[{name:'shared_scalar_point',lines:[2946,3044]},{name:'fixed_scales',lines:[3352,3405]},{name:'comparison_precision52',lines:[4160,4279]},{name:'scalar_order32',lines:[4285,4306]},{name:'quotient_domains',lines:[4311,4405]},{name:'direct_lucas',lines:[4575,4605]}]},fixedParameter:{name:'S',value:'3^(2^16)',coordinate:false},coordinates:coords,residuals,gates,values,guards,census,anchor:{rowId:anchorRow,privateCoordinateIds:anchor.map(idof),physicalA:encode(fa)},counts:{baseCoordinates:coords.filter(c=>c.kind==='base'||c.kind==='input').length,structuralResiduals:residuals.length-gates.length,coordinates:coords.length,residuals:residuals.length,gates:gates.length}};
data.variant={name:'height49_over8_pade21_linear_delta_leaves',status:'pending_independent_emitted_review',input:'3723*(2X+1)^2',normalizer:114444,scalarIndexOrder:8,highApproximation:'Pade(2,1)',inheritedCheckpoint:'v10-height49over8-326',normChainLeafSemantics:tests.map((t,j)=>({testIndex:j,order:t.order,kind:t.parityLeaf?'even_valuation_reciprocal_delta':'square'}))};
fs.writeFileSync(path.join(OUT,'raw-ir.json'),JSON.stringify(data,null,2)+'\n');
// An equivalent translated system. This is 16 times the original anchor
// after u=S+(U-3V+3W)/4,v=S/2+V/4,w=3S/2+W/4.
let translated=JSON.parse(JSON.stringify(data));let[u,v,w]=anchor;
translated.residuals[anchorRow].terms=encode(add(scale(sq(fa),-48),sq(u),scale(mul(u,v),-6),scale(mul(u,w),6),scale(sq(v),15),scale(mul(v,w),-18),scale(sq(w),7),mul(term(8,[],1),u)));
translated.residuals[anchorRow].name='anchor.translatedEquation';translated.anchor.translation={oldU:'S+(U-3V+3W)/4',oldV:'S/2+V/4',oldW:'3S/2+W/4',newRowEquals:'16*oldRowAfterSubstitution',determinant:'1/64'};
translated.coordinates[anchor.map(idof)[0]].name='anchor.U';translated.coordinates[anchor.map(idof)[1]].name='anchor.V';translated.coordinates[anchor.map(idof)[2]].name='anchor.W';
fs.writeFileSync(path.join(OUT,'raw-translated-ir.json'),JSON.stringify(translated,null,2)+'\n');
fs.writeFileSync(path.join(OUT,'census.json'),JSON.stringify({counts:data.counts,blocks:census},null,2)+'\n');
console.log(JSON.stringify({counts:data.counts,census},null,2));
