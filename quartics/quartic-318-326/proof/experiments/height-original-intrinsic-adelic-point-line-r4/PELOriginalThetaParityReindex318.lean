module
public import PELOriginalLevelTheta318
public section
noncomputable section
namespace PELOriginalThetaParityReindex318
open QuaternionicRealPeriod318 PELOriginalThetaConvergence318 PELOriginalLevelTheta318

/-- The integral image of (m,n)↦(m+n,m−n): the two resulting frequencies
have the SAME full two-coordinate parity, not just one scalar parity. -/
abbrev ParityPairs:={p:Index×Index // residue 2 p.1=residue 2 p.2}
@[expose] def halves (k l:Index):Index×Index:=
  (((k.1+l.1)/2,(k.2+l.2)/2),((k.1-l.1)/2,(k.2-l.2)/2))
lemma parity_of_sum_difference (m n:Index):residue 2 (m+n)=residue 2 (m-n):=by
  apply Prod.ext
  · apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
    change (m.1+n.1)%2=(m.1-n.1)%2
    omega
  · apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mpr
    change (m.2+n.2)%2=(m.2-n.2)%2
    omega
lemma halves_sum_difference (m n:Index):halves (m+n) (m-n)=(m,n):=by
  apply Prod.ext <;> apply Prod.ext <;> simp only [halves,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub] <;> omega
lemma sum_difference_halves (k l:Index) (h:residue 2 k=residue 2 l):
    ((halves k l).1+(halves k l).2,(halves k l).1-(halves k l).2)=(k,l):=by
  have h0:k.1%2=l.1%2:=(ZMod.intCast_eq_intCast_iff' _ _ 2).mp (congrArg Prod.fst h)
  have h1:k.2%2=l.2%2:=(ZMod.intCast_eq_intCast_iff' _ _ 2).mp (congrArg Prod.snd h)
  apply Prod.ext <;> apply Prod.ext <;> simp only [halves,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub] <;> omega
@[expose] def parityEquiv:(Index×Index)≃ParityPairs where
  toFun p:=⟨(p.1+p.2,p.1-p.2),parity_of_sum_difference p.1 p.2⟩
  invFun p:=halves p.1.1 p.1.2
  left_inv p:=halves_sum_difference p.1 p.2
  right_inv p:=Subtype.ext (sum_difference_halves p.1.1 p.1.2 p.2)

abbrev ResidueFiber (r:Label 2):={k:Index // residue 2 k=r}
/-- Exact integral-frequency partition into the FOUR common parity
classes. Both inverse maps retain all integer frequencies. -/
@[expose] def residueEquiv:ParityPairs≃Σr:Label 2,ResidueFiber r×ResidueFiber r where
  toFun p:=⟨residue 2 p.1.1,⟨p.1.1,rfl⟩,⟨p.1.2,p.2.symm⟩⟩
  invFun p:=⟨(p.2.1.val,p.2.2.val),p.2.1.property.trans p.2.2.property.symm⟩
  left_inv p:=rfl
  right_inv p:=by
    rcases p with ⟨r,⟨k,hk⟩,⟨l,hl⟩⟩
    dsimp
    subst r
    rfl
@[expose] def completeEquiv:(Index×Index)≃Σr:Label 2,ResidueFiber r×ResidueFiber r:=
  parityEquiv.trans residueEquiv

/-- Exact summand identity underlying the genus-two addition formula.
No finite truncation, interchange of conditionally convergent sums, or
unimodular assertion about the determinant-four transformation is used. -/
lemma summand_identity (τ:ℂ) (m n:Index) (z a:ComplexVectors):
    term τ m (z+a)*term τ n (z-a)=
      PELOriginalScaledThetaConvergence318.term τ (1/(2:ℝ)) (m+n) z*
        PELOriginalScaledThetaConvergence318.term τ (1/(2:ℝ)) (m-n) a:=by
  simp only [term,PELOriginalScaledThetaConvergence318.term,←Complex.exp_add]
  congr 1
  simp only [quadratic,linear,Pi.add_apply,Pi.sub_apply,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub]
  push_cast
  ring
end PELOriginalThetaParityReindex318
