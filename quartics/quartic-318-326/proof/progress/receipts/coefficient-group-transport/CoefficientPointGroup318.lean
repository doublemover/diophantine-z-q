module
public import CoefficientSchemePoints318
public section
noncomputable section
namespace CoefficientPointGroup318
open AlgebraicGeometry CategoryTheory
open CoefficientSchemePoints318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S]
variable {T:Scheme} (b:T ⟶ Spec (CommRingCat.of S))

theorem sum_assoc (p q r:Points N S b) : sum N S b (sum N S b p q) r=sum N S b p (sum N S b q r) := by
  apply forget_injective N S b
  simp only [forget_sum]
  exact LiteralSchemePointAssociativity318.sum_assoc N _ _ _ _
theorem zero_sum (p:Points N S b) : sum N S b (zero N S b) p=p := by
  apply forget_injective N S b
  simp only [forget_sum,forget_zero]
  exact LiteralSchemePointOperations318.zero_sum N _ _
theorem sum_zero (p:Points N S b) : sum N S b p (zero N S b)=p := by
  apply forget_injective N S b
  simp only [forget_sum,forget_zero]
  exact LiteralSchemePointOperations318.sum_zero N _ _
theorem neg_sum (p:Points N S b) : sum N S b (neg N S b p) p=zero N S b := by
  apply forget_injective N S b
  simp only [forget_sum,forget_neg,forget_zero]
  exact LiteralSchemePointOperations318.neg_sum N _ _
theorem sum_comm (p q:Points N S b) : sum N S b p q=sum N S b q p := by
  apply forget_injective N S b
  simp only [forget_sum]
  exact LiteralSchemePointOperations318.sum_comm N _ _ _
instance : Add (Points N S b) := ⟨sum N S b⟩
instance : Zero (Points N S b) := ⟨zero N S b⟩
instance : Neg (Points N S b) := ⟨neg N S b⟩
/-- Actual represented points of every coefficient-changed literal family
form an abelian group, including on nonreduced or nonaffine Scheme tests. -/
instance group : AddCommGroup (Points N S b) where
  add:=sum N S b
  zero:=zero N S b
  neg:=neg N S b
  nsmul:=nsmulRec
  zsmul:=zsmulRec
  add_assoc:=sum_assoc N S b
  zero_add:=zero_sum N S b
  add_zero:=sum_zero N S b
  neg_add_cancel:=neg_sum N S b
  add_comm:=sum_comm N S b

/-- The base-change point equivalence is additive for the actual additions,
not an arbitrary relabeling of finite points. -/
@[expose] def addEquiv : Points N S b ≃+
    LiteralSchemePointOperations318.Points N
      (b ≫ Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) S))) where
  __:=CoefficientSchemePoints318.equiv N S b
  map_add':=forget_sum N S b
end CoefficientPointGroup318
