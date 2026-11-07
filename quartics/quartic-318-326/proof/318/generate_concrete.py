"""Emit the exact final residual data into a typed Lean sparse-quartic module.
Each coordinate follows the supplied compact map."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,sys,re
folder=Path(sys.argv[1]);out=Path(sys.argv[2])
irfile=folder/'compiled-ir.json';ir=json.loads(irfile.read_text())
cm=json.loads((folder/'coordinate-map.json').read_text())
mp={c['sourceId']:c['compactId'] for c in cm['mapping']}
param=ir['fixedParameter']['value']; assert re.fullmatch(r'3\^\(2\^\d+\)',param),param
n=len(mp);assert sorted(mp.values())==list(range(n));assert mp[0]==0
lines=['module','', 'public import SparseQuartic','', 'public section','', 'namespace CurrentPolynomial','',
 'set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
 '/- Exact residual syntax from '+str(irfile)+'.',
 'Source SHA256: '+hashlib.sha256(irfile.read_bytes()).hexdigest()+'.',
 'This data declaration and the theorems below do not prove the arithmetic source characterization. -/', '',
 '']
termcount=0
for k,r in enumerate(ir['residuals']):
 lines+=['-- '+r['name'], '@[expose] def row'+str(k)+' : List (SparseQuartic.Term '+str(n)+') := [']
 for l,t in enumerate(r['terms']):
  a=Fraction(t['coefficient']);assert a.denominator==1
  mon=[mp[v] for v in t['monomial']];assert len(mon)<=2 and all(0<=v<n for v in mon)
  m='.one' if not mon else ('.linear '+str(mon[0]) if len(mon)==1 else '.quadratic '+str(mon[0])+' '+str(mon[1]))
  lines.append('    ⟨'+str(a.numerator)+', '+str(t.get('sPower',0))+', '+m+'⟩'+(',' if l<len(r['terms'])-1 else ''))
  termcount+=1
 lines.append(']\n')
lines+= ['@[expose] def rows : List (List (SparseQuartic.Term '+str(n)+')) := ['+', '.join('row'+str(k) for k in range(len(ir['residuals'])))+']','', 'def scale : ℤ := '+param,'',
 '@[expose] noncomputable def P : MvPolynomial (Fin '+str(n)+') ℤ := SparseQuartic.polynomial scale rows','',
 'theorem row_count : rows.length = '+str(len(ir['residuals']))+' := by decide','',
 'theorem coordinate_degree_le_four : P.totalDegree ≤ 4 := SparseQuartic.polynomial_degree scale rows','',
 'theorem zero_iff_constraints (w : Fin '+str(n)+' → ℚ) :',
 '    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w P = 0 ↔ SparseQuartic.Constraints scale rows w :=',
 '  SparseQuartic.polynomial_zero_iff scale rows w','',
 'theorem input_projection_iff (q : ℚ) :',
 '    (∃ w : Fin '+str(n-1)+' → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q w) P = 0) ↔',
 '    ∃ w : Fin '+str(n-1)+' → ℚ, SparseQuartic.Constraints scale rows (Fin.cons q w) :=',
 '  SparseQuartic.polynomial_witnesses_iff scale rows q','',
 '/-- This theorem explicitly requires the arithmetic characterization of the',
 'concrete source residuals. The hypothesis is NOT proved in this module. -/',
 'theorem defines_integers_of_source',
 '    (source : ∀ q : ℚ, (∃ w : Fin '+str(n-1)+' → ℚ, SparseQuartic.Constraints scale rows (Fin.cons q w)) ↔',
 '      ∃ z : ℤ, (z : ℚ) = q) :',
 '    ∀ q : ℚ, (∃ w : Fin '+str(n-1)+' → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q w) P = 0) ↔',
 '      ∃ z : ℤ, (z : ℚ) = q := by',
 '  intro q', '  exact (input_projection_iff q).trans (source q)','', 'end CurrentPolynomial','']
out.write_text('\n'.join(lines).replace('CurrentPolynomial',out.stem))
report={'source':str(irfile),'sourceSha256':hashlib.sha256(irfile.read_bytes()).hexdigest(),'coordinates':n,'rows':len(ir['residuals']),'terms':termcount,'generatedFile':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'scope':'Literal typed quadratic residual data plus generic SOS and degree proofs; arithmetic source hypothesis unproved.'}
out.with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
