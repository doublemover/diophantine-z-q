from pathlib import Path
import json,re,sys
folder=Path(sys.argv[1]) if len(sys.argv)>1 else Path('../candidates/normalized-794/compiled')
RP=sys.argv[2] if len(sys.argv)>2 else 'ConcreteReplay'
PP=sys.argv[3] if len(sys.argv)>3 else 'CurrentPolynomial'
BN=sys.argv[4] if len(sys.argv)>4 else 'ConcreteBridge'
ir=json.loads((folder/'compiled-ir.json').read_text());cm=json.loads((folder/'coordinate-map.json').read_text());mp={e['compactId']:e['sourceId'] for e in cm['mapping']};n=len(mp)
info=json.loads(Path(RP+'.json').read_text());last=info['lastStage'];txt=Path(RP+'Data.lean').read_text();line=next(x for x in txt.splitlines() if x.startswith('@[expose] def '+last+' '));rnames=re.findall(r'\br\d+\b',line)
assert len(rnames)==len(ir['residuals'])
blocks=[];prev=mp[0]
for j in range(1,n):
 if mp[j]-j!=mp[j-1]-(j-1):blocks.append((j,mp[j-1]-(j-1)))
lastoffset=mp[n-1]-(n-1)
gaps=[]
for j in range(1,n):gaps.extend([j]*(mp[j]-mp[j-1]-1))
idx='j.val + CircuitReplay.gapOffset '+str(gaps)+' j.val'
head=['module','public import ConcreteReplay','public import CurrentPolynomial','public section','namespace ConcreteBridge','open CircuitReplay','set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option linter.unusedSimpArgs false','set_option linter.unnecessarySeqFocus false','set_option linter.unnecessarySimpa false',
 f'def index (j : Fin {n}) : ℕ := {idx}',
 'theorem index_injective : Function.Injective index := CircuitReplay.gapIndex_injective '+str(gaps),
 'theorem index_zero : index 0 = 0 := by decide']
proofs=[]
for k,r in enumerate(rnames):
 proofs.append(f'''theorem row{k}_identity (S : ℤ) (w : Assignment) :
    ConcreteReplay.{r} (S : ℚ) w =
      SparseQuartic.residualValue S (fun j => w (index j)) CurrentPolynomial.row{k} := by
  simp only [ConcreteReplay.{r}, CurrentPolynomial.row{k}, SparseQuartic.residualValue,
    SparseQuartic.termValue, SparseQuartic.monomialValue, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  norm_num [index, CircuitReplay.gapOffset] <;> ring
''')
rel=''.join(f'List.Forall₂.cons (fun w => (congrArg (fun x : ℚ => x = 0) (row{k}_identity S w)).to_iff) (\n' for k in range(len(rnames)))+'List.Forall₂.nil'+')'*len(rnames)
proofs+= [f'''theorem interpreted_constraints (S : ℤ) (w : Assignment) :
    Constraints (ConcreteReplay.{last} (S : ℚ)) w ↔
      SparseQuartic.Constraints S CurrentPolynomial.rows (fun j => w (index j)) := by
  have hrel : List.Forall₂ (fun f g : Row => ∀ w, f w = 0 ↔ g w = 0)
      (ConcreteReplay.{last} (S : ℚ))
      (CurrentPolynomial.rows.map (fun ts => fun w =>
        SparseQuartic.residualValue S (fun j => w (index j)) ts)) := by
    simp only [ConcreteReplay.{last}, CurrentPolynomial.rows, List.map_cons, List.map_nil]
    exact {rel}
  have h := constraints_congr _ _ hrel w
  simpa only [Constraints, SparseQuartic.Constraints, List.forall_mem_map] using h
''',f'''theorem final_solution_iff (S : ℤ) (q : ℚ) :
    HasSolution (ConcreteReplay.{last} (S : ℚ)) q ↔
      ∃ w : Fin {n-1} → ℚ, SparseQuartic.Constraints S CurrentPolynomial.rows (Fin.cons q w) :=
  finite_solution_iff index index_injective index_zero _ _ (interpreted_constraints S) q
''',f'''theorem polynomial_zero_iff_source (q : ℚ) :
    (∃ w : Fin {n-1} → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) CurrentPolynomial.P = 0) ↔
    HasSolution (ConcreteReplay.stage0 (CurrentPolynomial.scale : ℚ)) q := by
  exact (CurrentPolynomial.input_projection_iff q).trans
    ((final_solution_iff CurrentPolynomial.scale q).symm.trans
      (ConcreteReplay.source_iff_final (CurrentPolynomial.scale : ℚ) q).symm)
''',f'''/-- The source arithmetic hypothesis is explicitly separate from the concrete,
checked compiler replay and the polynomial's SOS semantics. -/
theorem defines_integers_of_source_arithmetic
    (sourceArithmetic : ∀ q : ℚ,
      HasSolution (ConcreteReplay.stage0 (CurrentPolynomial.scale : ℚ)) q ↔
        ∃ z : ℤ, (z : ℚ) = q) :
    ∀ q : ℚ, (∃ w : Fin {n-1} → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) CurrentPolynomial.P = 0) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  intro q
  exact (polynomial_zero_iff_source q).trans (sourceArithmetic q)
''']
Path(BN+'.lean').write_text(('\n\n'.join(head+proofs+['end ConcreteBridge'])+'\n').replace('ConcreteReplay',RP).replace('CurrentPolynomial',PP).replace('ConcreteBridge',BN));print(n,len(rnames),blocks)
