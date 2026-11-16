from pathlib import Path
import sympy as s,ast,re,json,hashlib,difflib,shutil
R=Path('arithmetic-20261114');S=R/'inner-relations-43676815887';E=Path('integration-20261114/repo/quartics/quartic-318-326/proof/experiments/original-infinity-range-extension-r9');H=Path('integration-next-43673862672/hosted-43676815887/experiment-original-infinity-range-extension-r9/progress-experiments/original-infinity-range-extension-r9');N='PELNormalizerInnerRelations318.lean';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n in ['before','after','own-hosted','primary']:(S/n).mkdir(parents=True,exist_ok=True)
b=(E/N).read_text();assert h(E/N)=='de87f87358afad0acca2fe2a14661c62dcb61d10c4de334a79c81460e5ff4dee'
prim=(E/'PELPrimeNormalizerRelations318.lean').read_text()
def coeff(name):return ast.literal_eval(re.search(r'def '+name+r' .*?:= (.*)',prim).group(1).replace('![','['))
sc=coeff('squareCoefficients');si=coeff('squareInverseCoefficients');cc=coeff('commutatorCoefficients')
r,i,j,k=s.symbols('r i j k');x=s.Matrix([r,i,j,k]);vs=[r,i,j,k];names=['re','imI','imJ','imK']
F=[s.Matrix([[1,0,0,0],[0,0,1,1],[0,0,1,0],[0,2,1,0]]),s.Matrix([[1,0,0,0],[0,1,2,0],[0,0,2,0],[0,0,1,2]]),s.Matrix([[1,0,0,0],[0,0,0,2],[0,0,1,0],[0,1,0,0]]),s.Matrix([[1,0,0,0],[0,2,0,0],[0,0,1,0],[0,0,2,2]])]
def mul(a,b):
 r,i,j,k=a;R,I,J,K=b
 return s.Matrix([r*R+2*j*J,r*I+i*R+2*k*J-2*j*K,r*J+j*R,r*K+k*R+i*J-j*I])
def red(a):return s.Matrix([a[0]-a[2],a[1]-a[3],-a[2],a[3]])
def expr(p):
 out=[]
 for v,n in zip(vs,names):
  c=int(s.expand(p).coeff(v))
  if c:out.append(f'({c})*x.{n}')
 return ' + '.join(out) or '0'
rows=[];blocks={}
for kind in ['square','commutator']:
 proof=[]
 for a in range(4):
  for bidx in (range(4) if kind=='commutator' else [a]):
   lhs=F[a]*F[bidx]*x
   rhs=mul(mul(red(cc[a][bidx] if kind=='commutator' else sc[a]),F[bidx]*F[a]*x if kind=='commutator' else x),red(cc[bidx][a] if kind=='commutator' else si[a]))
   for z,name in enumerate(names):
    delta=s.expand(lhs[z]-rhs[z]);q=s.expand(delta/3)
    assert all(c.q==1 for c in s.Poly(q,vs).coeffs())
    assert s.expand(delta-3*q)==0
    rows.append({'kind':kind,'indices':[a,bidx] if kind=='commutator' else[a],'coordinate':name,'difference':str(delta),'h3_multiplier':str(q)})
    if delta==0:continue
    case=f'«{a}».'+(f'«{bidx}».' if kind=='commutator' else '')+name
    if kind=='square' and a==2 and name in ['imI','imK']:proof.append(f'  case {case} => simp only [h3,or_true]')
    else:proof.append(f'  case {case} => linear_combination ({expr(q)})*h3')
 blocks[kind]='\n'.join(proof)+'\n'
a=b.replace(' := by\n  change forward',' := by\n  have h3 : (3:F3)=0 := by decide\n  change forward')
a=a.replace('norm_num [forward,reduceCoordinates,squareCoefficients,squareInverseCoefficients] <;> ring\n','norm_num [forward,reduceCoordinates,squareCoefficients,squareInverseCoefficients] <;> ring\n'+blocks['square'])
a=a.replace('norm_num [forward,reduceCoordinates,commutatorCoefficients] <;> ring\n','norm_num [forward,reduceCoordinates,commutatorCoefficients] <;> ring\n'+blocks['commutator'])
(S/'before'/N).write_text(b);(S/'after'/N).write_text(a);(S/'SOURCE.diff').write_text(''.join(difflib.unified_diff(b.splitlines(True),a.splitlines(True),fromfile='before/'+N,tofile='after/'+N)))
for p,n in [(E/'intake.json','predecessor-intake.json'),(H/'RESULT.json','RESULT.json'),(H/'logs'/N.replace('.lean','.log'),N.replace('.lean','.log'))]:shutil.copy2(p,S/'own-hosted'/n)
d=json.loads((E/'intake.json').read_text());rr=json.loads((H/'RESULT.json').read_text());assert rr['packet_sha256']==h(E/'intake.json');assert d['files'][N]['sha256']==h(S/'before'/N)
for n in ['PELPrimeNormalizerRelations318','PELOrderReductionThree318','PELNormalizerReductionAction318','PELNormalizerResidueFrobenius318'] :shutil.copy2(E/(n+'.lean'),S/'primary'/(n+'.lean'))
(S/'POLYNOMIAL-CHECK.json').write_text(json.dumps({'scope':'80 full symbolic coordinate identities over characteristic3; not Lean','identities':rows,'all_differences_are_explicit_multiples_of_3':True},indent=2)+'\n');shutil.copy2(__file__,S/'check_and_generate.py')
clauses=[
'Inputs: exactly every i,j:Fin4 and arbitrary x in the original entire Reduction=QuaternionAlgebra (ZMod3) 0 0 2. No finite-field coordinate enumeration or restriction to units/residue field.',
'Construction: retain literal original squareUnit, its actual inverse, commutatorUnit and reverse commutator inverse. Their coefficient arrays and original order/ring reduction are unchanged.',
'Domain: all4 square cases, all16 ordered pairs, and all4 symbolic coordinates are checked. Diagonal pairs already close in the unchanged ring proof; all residual cases now have explicit characteristic3 certificates.',
'Maps: exact reductionEquiv/forward composition and multiplication order unit*x*unit_inverse remain unchanged. This is inner-action equality, not a falsely trivial/commuting action.',
'Coefficients: introduce only the closed true native fact (3:F3)=0, by decide. Every remaining polynomial difference is an explicit integer linear combination of arbitrary x.re,x.imI,x.imJ,x.imK times that fact. The two actual disjunctive residuals close by their literal 3=0 disjunct. No norm/scalar is modified.',
'Exceptions: all original quaternion coordinates including nonunits and nilpotent directions remain. Existing inverse type annotations from previous repair and original1800000 heartbeat option are retained; no resource increase/import/telescope change.',
'Consumer: both full original square_inner and commutator_inner statements are unchanged. Actual inner correction units are preserved rather than quotiented away or assumed central.',
'Actual evidence: own infinity9 at HEAD9582519df0fe15c6e01c86d935a85a9a5257eb8d/run43676815887 passes Frobenius then fails InnerRelations19.564s. Previous inverse synthesis errors are gone; log supplies16 square and48 off-diagonal coordinate residuals. This candidate closes their characteristic3 arithmetic; no module pass claimed.',
'Verification: symbolic rational/integer polynomial checker derives80 exact coefficient differences from the bound original unit arrays and actual forward matrices, all divisible by3; this is independent arithmetic evidence, not Lean. Own RESULT/intake/log bound; independent source/current review required. No local Lean/Lake, active source edits, new trust or research activation.']
(S/'APPLICATION.md').write_text('# Current full reduction inner relations\n\n'+''.join(f'{idx+1}. {c}\n\n' for idx,c in enumerate(clauses)))
m={str(p.relative_to(S)):h(p) for p in sorted(S.rglob('*')) if p.is_file() and p.name!='BINDINGS.json'};(S/'BINDINGS.json').write_text(json.dumps(m,indent=2)+'\n');print(h(S/'after'/N),h(S/'BINDINGS.json'),len(m),len(rows))
