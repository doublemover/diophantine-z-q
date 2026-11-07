"""Generate kernel-checkable Lean proofs of exact IR transformations.
Every emitted row identity is proved using Lean's ring procedure."""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json,sys,hashlib
ROOT=Path(__file__).resolve().parent.parent
source=ROOT/'candidates/reciprocal-tiny-norm-pair/compiled/compiled-ir.json'
combined=ROOT/'candidates/combined-reciprocal-tiny-norm-pair'
nonlinear=ROOT/'searches/nonlinear796/pass1'
raw_direct = len(sys.argv)>1 and sys.argv[1]=='--raw-direct'
if len(sys.argv)>1 and sys.argv[1] in ['--direct','--raw-direct']:
 source=Path(sys.argv[2]);combined=None;nonlinear=Path(sys.argv[3]);OUT=Path(sys.argv[4])
else:
 if len(sys.argv)>3:source,combined,nonlinear=map(Path,sys.argv[1:4])
 OUT=Path(sys.argv[4]) if len(sys.argv)>4 else Path('ConcreteReplay.lean')
NAMESPACE=OUT.stem
anchor_value_dir=Path(sys.argv[sys.argv.index('--anchor-value-dir')+1]) if '--anchor-value-dir' in sys.argv else None
def load(p):return json.loads(Path(p).read_text())
def clean(p):return {k:v for k,v in p.items() if v}
def poly(ts):
 p=defaultdict(F)
 for t in ts:p[tuple(t['monomial']),t.get('sPower',0)]+=F(t['coefficient'])
 return clean(p)
def rows(x):return {r['id']:poly(r['terms']) for r in x['residuals']}
def add(p,q,f=F(1)):
 r=defaultdict(F,p)
 for k,v in q.items():r[k]+=f*v
 return clean(r)
def mul(p,q):
 r=defaultdict(F)
 for (a,s),x in p.items():
  for (b,t),y in q.items():r[tuple(sorted(a+b)),s+t]+=x*y
 return clean(r)
def scale(p,c):return clean({k:v*c for k,v in p.items()})
def sub(p,i,q):
 r={}
 for (m,s),c in p.items():
  t={((),s):c}
  for v in m:t=mul(t,q if v==i else {((v,),0):F(1)})
  r=add(r,t)
 return r
def key(p):return tuple(sorted(p.items()))
def coeff(c):return str(c.numerator) if c.denominator==1 else '('+str(c.numerator)+' / '+str(c.denominator)+')'
def expr(p):
 return ' + '.join('('+coeff(c)+''.join(' * w '+str(v) for v in m)+(' * S^'+str(s) if s else '')+')' for (m,s),c in sorted(p.items())) or '0'
D=[];P=[];reg={};stage=0
head=['module','public import '+('AnchorValueShear' if anchor_value_dir is not None else ('AffineAnchor' if raw_direct else 'CircuitReplay')),'public section','namespace '+NAMESPACE,'open CircuitReplay','set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option linter.unusedSimpArgs false','set_option linter.unusedVariables false','set_option linter.unnecessarySimpa false','set_option linter.unnecessarySeqFocus false','']
def row(p):
 k=key(p)
 if k not in reg:
  name='r'+str(len(reg));reg[k]=name;D.append('def '+name+' (S : ℚ) (w : Assignment) : ℚ := '+expr(p))
 return reg[k]
def ref(p):return row(p)+' S'
def lst(rs):return '['+', '.join(ref(p) for p in rs.values())+']'
def st(rs):
 global stage
 name='stage'+str(stage);stage+=1;D.append('def '+name+' (S : ℚ) : List Row := '+lst(rs));return name
# Every local expression identity is kernel-checked by ring.
def roweq(a,b,transform=None):
 ra,rb=row(a),row(b)
 if key(a)==key(b) and (not transform or not any(v in transform[2] for m,sp in b for v in m)):return '(fun _ => Iff.rfl)'
 if transform:
  trans,unfolds,active=transform
  stmt=f'{ra} S w = {rb} S ({trans} w)'
  proof=f'by simp only [{ra}, {rb}, {", ".join(unfolds)}] <;> norm_num <;> ring'
 else:
  c=next(iter(a.values()))/b[next(iter(a))] if a else F(1)
  assert a==scale(b,c)
  stmt=f'{ra} S w = ({coeff(c)} : ℚ) * {rb} S w'
  proof=f'by unfold {ra} {rb}; ring'
 if transform:return f'(by intro w; have h : {stmt} := ({proof}); simpa only [Function.comp_def, h])'
 return f'(by intro w; have h : {stmt} := ({proof}); rw [h]; exact mul_eq_zero.trans (by norm_num))'
def listrel(aa,bb,transform=None):
 assert list(aa)==list(bb)
 parts=[roweq(aa[i],bb[i],transform) for i in aa]
 return ''.join('List.Forall₂.cons '+p+' (\n' for p in parts)+'List.Forall₂.nil'+')'*len(parts)
def congr(sa,sb,aa,bb,transform=None,append=None):
 name='congr'+str(len(P))
 right=f'({sb} S).map (fun f => f ∘ {transform[0]})' if transform else f'{sb} S'
 P.append(f'''theorem {name} (S : ℚ) : ∀ q, HasSolution ({sa} S) q ↔ HasSolution ({right}) q := by
  apply solutions_congr
  apply constraints_congr
  simp only [{sa}, {sb}, List.map_cons, List.map_nil]
  exact {listrel(aa,bb,transform)}
''')
 return name
current=rows(load(source));start=st(current);cur=start;chain=[]
def normalized(target):
 global current,cur
 dst=st(target);h=congr(dst,cur,target,current);chain.append(f'({h} S q).symm');cur=dst;current=target
def apply_shear(base,high,factor):
 global current,cur
 old=current.copy();new=old.copy()
 for i in high:
  replacement={((i,),0):F(1),((base,),0):factor}
  new={j:sub(p,i,replacement) for j,p in new.items()}
 dst=st(new);trans=f'(shear {base} {high} ({coeff(factor)}))';h=congr(dst,cur,new,old,(trans,['CircuitReplay.shear'],set(high)))
 chain.append(f'(shear_solutions ({cur} S) {base} {high} (by decide) (by decide) ({coeff(factor)}) q).trans ({h} S q).symm')
 current=new;cur=dst
if combined is not None:
 for shear in load(combined/'AFFINE_SHEAR_CERTIFICATE.json')['maps']:
  apply_shear(shear['base'],shear['highs'],F(-1))
 assert current==rows(load(combined/'sheared-ir.json'))

def elim(op):
 global current,cur
 i=op['coordinate'];pivot=op['pivot'];r=poly(op['replacement']);p=current[pivot]
 rel=add({((i,),0):F(1)},r,F(-1));c=p[((i,),0)];assert p==scale(rel,c)
 assert all(i not in m for m,s in r)
 keys=list(current);idx=keys.index(pivot);a={j:current[j] for j in keys[:idx]};b={j:current[j] for j in keys[idx+1:]};rest=a|b
 new={j:sub(q,i,r) for j,q in rest.items()};dst=st(new)
 restname=st(rest);rn=row(r);pn=row(p)
 h=congr(dst,restname,new,rest,(f'(replace {i} ({rn} S))',['CircuitReplay.replace','Function.update',rn],{i}))
 name='elimination'+str(len(P))
 P.append(f'''theorem {name} (S : ℚ) (q : ℚ) : HasSolution ({cur} S) q ↔ HasSolution ({dst} S) q := by
  have hp : ∀ w, {pn} S w = ({coeff(c)} : ℚ) * (w {i} - {rn} S w) := by
    intro w; unfold {pn} {rn}; ring
  have hr : ∀ w, {rn} S (replace {i} ({rn} S) w) = {rn} S w := by
    intro w; simp [{rn}, replace]
  have he := eliminate ({pn} S) ({rn} S) ({restname} S) {i} ({coeff(c)}) (by decide) (by norm_num) hp hr q
  have hm := move_pivot ({lst(a)}) ({lst(b)}) ({pn} S) q
  change HasSolution ({cur} S) q ↔ HasSolution ({dst} S) q
  exact hm.trans (he.trans ({h} S q).symm)
''')
 chain.append(f'{name} S q');current=new;cur=dst
if raw_direct:
 # Replay the exact source anchor translation before compiler normalization.
 # Substitution is simultaneous, since the U expression also contains V and W.
 rawdata=load(source); translated=load(source.parent/'raw-translated-ir.json')
 a=rawdata['anchor'];u,v,z=a['privateCoordinateIds'];rid=a['rowId']
 assert translated['anchor']['translation']=={'oldU':'S+(U-3V+3W)/4','oldV':'S/2+V/4','oldW':'3S/2+W/4','newRowEquals':'16*oldRowAfterSubstitution','determinant':'1/64'}
 scaled=current.copy();scaled[rid]=scale(scaled[rid],F(16));normalized(scaled)
 repl={u:{((),1):F(1),((u,),0):F(1,4),((v,),0):F(-3,4),((z,),0):F(3,4)},v:{((),1):F(1,2),((v,),0):F(1,4)},z:{((),1):F(3,2),((z,),0):F(1,4)}}
 def simultaneous(p):
  result={}
  for (m,sp),c in p.items():
   term={((),sp):c}
   for i in m:term=mul(term,repl.get(i,{((i,),0):F(1)}))
   result=add(result,term)
  return result
 new={j:simultaneous(p) for j,p in current.items()}
 assert new==rows(translated)
 dst=st(new);trans=f'(AffineAnchor.forward {u} {v} {z} S)'
 h=congr(dst,cur,new,current,(trans,['AffineAnchor.forward'],{u,v,z}))
 chain.append(f'(AffineAnchor.solutions ({cur} S) {u} {v} {z} (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S q).trans ({h} S q).symm')
 current=new;cur=dst
 # Replay compiler scalings in batches, and derive each constant pivot exactly.
 # Each generated batch/pivot identity is separately checked by Lean.
 cert=load(source.parent/'compiled/reduction-certificate.json')
 assert cert['inputSha256']==hashlib.sha256((source.parent/'raw-translated-ir.json').read_bytes()).hexdigest()
 pending=current.copy()
 for cop in cert['operations']:
  if cop['kind']=='normalize':
   factor=F(cop['multiplier']);assert factor
   pending[cop['residual']]=scale(pending[cop['residual']],factor)
  elif cop['kind']=='eliminate':
   if pending!=current:normalized(pending)
   elim(cop);pending=current.copy()
  else:raise AssertionError('Unsupported raw compiler operation: '+cop['kind'])
 if pending!=current:normalized(pending)
 assert current==rows(load(source.parent/'compiled/compiled-ir.json'))
if anchor_value_dir is not None:
 cert=load(anchor_value_dir/'shear-certificate.json')
 original=Path(cert['source'])
 assert hashlib.sha256(original.read_bytes()).hexdigest()==cert['sourceSha256']
 assert current==rows(load(original))
 u,n=cert['coordinate'],cert['normCoordinate']
 images={u:{((u,),0):F(1),((n,),1):F(-1)},n:{((n,),0):F(1,4096)}}
 def anchored_sub(p):
  result={}
  for (mon,sp),c in p.items():
   term={((),sp):c}
   for i in mon:term=mul(term,images.get(i,{((i,),0):F(1)}))
   result=add(result,term)
  return result
 new={j:anchored_sub(p) for j,p in current.items()}
 assert new==rows(load(anchor_value_dir/'sheared-ir.json'))
 dst=st(new);trans=f'(AnchorValueShear.forward {u} {n} S)'
 h=congr(dst,cur,new,current,(trans,['AnchorValueShear.forward'],{u,n}))
 chain.append(f'(AnchorValueShear.solutions ({cur} S) {u} {n} (by decide) (by decide) (by decide) S q).trans ({h} S q).symm')
 current=new;cur=dst
 cc=load(anchor_value_dir/'compiled/reduction-certificate.json');pending=current.copy()
 assert cc['inputSha256']==hashlib.sha256((anchor_value_dir/'sheared-ir.json').read_bytes()).hexdigest()
 for cop in cc['operations']:
  if cop['kind']=='normalize':
   factor=F(cop['multiplier']);assert factor
   pending[cop['residual']]=scale(pending[cop['residual']],factor)
  elif cop['kind']=='eliminate':
   if pending!=current:normalized(pending)
   elim(cop);pending=current.copy()
  else:raise AssertionError('Unsupported shear compiler operation: '+cop['kind'])
 if pending!=current:normalized(pending)
 assert current==rows(load(anchor_value_dir/'compiled/compiled-ir.json'))
if combined is not None:
 for op in load(combined/'shear-elimination-certificate.json')['operations']:elim(op)
 assert current==rows(load(combined/'two-eliminated-ir.json'))
 normalized(rows(load(combined/'compiled/compiled-ir.json')))
if (nonlinear/'source-ir.json').exists():assert current==rows(load(nonlinear/'source-ir.json'))
# The nonlinear eliminations are followed by certified additions of multiples of
# unchanged rows. Their identities are also proved by ring, never trusted JSON.
for op in load(nonlinear/'modulo-certificate.json')['operations']:
 if op.get('kind')=='shear':
  groups={}
  for sh in op['shears']:groups.setdefault(F(sh['factor']),[]).append(sh['coordinate'])
  for factor,high in groups.items():apply_shear(op['free'],high,factor)
  continue
 elim(op)
 for ch in op['changes']:
  j=ch['row'];p=current[j];r=poly(ch['result']);comb={}
  for x in ch['multiples']:comb=add(comb,mul(poly(x['factor']),current[x['row']]))
  delta=add(p,r,F(-1));sign=1 if delta==comb else -1;assert delta==scale(comb,F(sign))
  keys=list(current);idx=keys.index(j);a={z:current[z] for z in keys[:idx]};b={z:current[z] for z in keys[idx+1:]};rest=a|b
  new=current|{j:r};dst=st(new);pn=row(p);rn=row(r);name='modulo'+str(len(P))
  hyps=[]
  for t,x in enumerate(ch['multiples']):
   pos=list(rest).index(x["row"])
   hyps.append(f'  have h{t} : {ref(current[x["row"]])} w = 0 := hw _ (List.get_mem ({lst(a)} ++ {lst(b)}) ⟨{pos}, by simp⟩)')
  lhs=' + '.join(f'({expr(poly(x["factor"]))}) * ({ref(current[x["row"]])} w)' for x in ch['multiples']) or '0'
  defs=', '.join(sorted({pn,rn}|{row(current[x['row']]) for x in ch['multiples']}))
  P.append(f'''theorem {name} (S : ℚ) (q : ℚ) : HasSolution ({cur} S) q ↔ HasSolution ({dst} S) q := by
  apply replace_row ({lst(a)}) ({lst(b)}) ({pn} S) ({rn} S) (q := q)
  intro w hw
{chr(10).join(hyps)}
  have hid : {pn} S w - {rn} S w = ({sign} : ℚ) * ({lhs}) := by
    simp only [{defs}]; ring
  simp only [{', '.join(['h'+str(t) for t in range(len(ch['multiples']))]+['mul_zero','add_zero'])}] at hid
  exact sub_eq_zero.mp hid
''')
  chain.append(f'{name} S q');current=new;cur=dst
assert current==rows(load(nonlinear/'candidate-ir.json'))
normalized(rows(load(nonlinear/'integer-candidate-ir.json')))
if (nonlinear/'polynomial/compiled-ir.json').exists():
 finalrows=rows(load(nonlinear/'polynomial/compiled-ir.json'))
 if finalrows!=current:normalized(finalrows)
P.append(f'theorem source_iff_final (S q : ℚ) : HasSolution ({start} S) q ↔ HasSolution ({cur} S) q := by\n  exact '+'.trans ('.join('('+x+')' for x in chain)+')'*(len(chain)-1)+'\n')
OUT.write_text('\n\n'.join(head+['@[expose] '+d for d in D]+P+['end '+NAMESPACE])+'\n')
modulebase=OUT.stem
Path(modulebase+'Data.lean').write_text('\n\n'.join(head+['@[expose] '+d for d in D]+['end '+NAMESPACE])+'\n')
previous=modulebase+'Data'
parts=[]
for i,proof in enumerate(P):
 name=modulebase+'Step'+str(i)
 h=head.copy();h[1]='public import '+previous
 Path(name+'.lean').write_text('\n\n'.join(h+[proof,'end '+NAMESPACE])+'\n')
 parts.append(name);previous=name
Path(modulebase+'Modules.json').write_text(json.dumps([modulebase+'Data']+parts))

OUT.with_suffix('.json').write_text(json.dumps({'source':str(source),'lastStage':cur,'rowDefinitions':len(reg),'proofBlocks':len(P),'stages':stage,'sourceSha256':hashlib.sha256(source.read_bytes()).hexdigest(),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest()},indent=2)+'\n')
print(OUT,len(reg),len(P),stage)
