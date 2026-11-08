module
public import LiteralSchemePointAssociativity318
public import CompletedIteratedAddition318
public section
noncomputable section
namespace LiteralSchemeCancellation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralSchemePointOperations318 LiteralSchemePointAssociativity318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {T:Scheme}
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "pE" => WeierstrassGluing318.structureMap A B
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
variable (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
/-- Cancellation for actual maps from arbitrary test Schemes over the literal
base, derived from the checked Scheme-map group diagrams. -/
theorem sum_left_cancel (p q r:Points N b) (h:sum N b p q=sum N b p r) : q=r := by
  have hh:=congrArg (fun s=>sum N b (neg N b p) s) h
  simpa only [←sum_assoc,neg_sum,zero_sum] using hh

theorem sum_eq_zero_iff (p q:Points N b) :
    sum N b p q=zero N b ↔ p=neg N b q := by
  constructor
  · intro h
    calc
      p=sum N b p (zero N b) := (sum_zero N b p).symm
      _=sum N b p (sum N b q (neg N b q)) :=
        congrArg (fun s=>sum N b p s) (sum_neg N b q).symm
      _=sum N b (sum N b p q) (neg N b q) := (sum_assoc N b p q (neg N b q)).symm
      _=sum N b (zero N b) (neg N b q) := congrArg (fun s=>sum N b s (neg N b q)) h
      _=neg N b q := zero_sum N b (neg N b q)
  · rintro rfl
    exact neg_sum N b q

theorem pair_diagonal (p:Points N b) : pair N b p p=p.val ≫ CompletedIteratedAddition318.diagonal A B := by
  apply pullback.hom_ext
  · simp only [pair_fst,Category.assoc,CompletedIteratedAddition318.diagonal_fst,Category.comp_id]
  · simp only [pair_snd,Category.assoc,CompletedIteratedAddition318.diagonal_snd,Category.comp_id]
theorem double_value (p:Points N b) :
    (sum N b p p).val=p.val ≫ CompletedIteratedAddition318.doubling A B hD := by
  change pair N b p p ≫ CompletedAddition318.addition A B hD=_
  rw [pair_diagonal,Category.assoc,CompletedIteratedAddition318.doubling]
theorem pair_triple (p:Points N b) : pair N b (sum N b p p) p=
    p.val ≫ CompletedIteratedAddition318.tripleInputs A B hD := by
  apply pullback.hom_ext
  · rw [pair_fst,Category.assoc,CompletedIteratedAddition318.tripleInputs_fst,double_value]
  · rw [pair_snd,Category.assoc,CompletedIteratedAddition318.tripleInputs_snd,Category.comp_id]
theorem triple_value (p:Points N b) :
    (sum N b (sum N b p p) p).val=p.val ≫ CompletedIteratedAddition318.tripling A B hD := by
  change pair N b (sum N b p p) p ≫ CompletedAddition318.addition A B hD=_
  rw [pair_triple,Category.assoc,CompletedIteratedAddition318.tripling]

theorem eq_iff_values (p q:Points N b) : p=q ↔ p.val=q.val := Subtype.ext_iff

/-- Exact morphism-level cancellation needed by the literal tripling fiber.
There is no affine, reducedness, or field hypothesis on the test Scheme T. -/
theorem tripling_zero_iff (t:T ⟶ WeierstrassGluing318.scheme A B) :
    t ≫ CompletedIteratedAddition318.tripling A B hD=t ≫ pE ≫ WeierstrassGluing318.infinity A B ↔
      t ≫ CompletedIteratedAddition318.doubling A B hD=t ≫ GluedNegation318.negation A B := by
  let b:=t ≫ pE
  let p:Points N b:=⟨t,rfl⟩
  have h:=sum_eq_zero_iff N b (sum N b p p) p
  simpa only [eq_iff_values,triple_value,double_value,neg,zero,p,b,Category.assoc] using h
end LiteralSchemeCancellation318
