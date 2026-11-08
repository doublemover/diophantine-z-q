module
public import LiteralSchemeCancellation318
public section
noncomputable section
namespace LiteralSchemePointGroup318
open AlgebraicGeometry CategoryTheory
open LiteralSchemePointOperations318 LiteralSchemePointAssociativity318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {T:Scheme}
variable (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))

instance : Add (Points N b) := ⟨sum N b⟩
instance : Zero (Points N b) := ⟨LiteralSchemePointOperations318.zero N b⟩
instance : Neg (Points N b) := ⟨neg N b⟩

/-- The actual represented points over every Scheme test form an abelian group;
the operations are precisely the already checked Scheme morphisms. -/
instance group : AddCommGroup (Points N b) where
  add := sum N b
  zero := LiteralSchemePointOperations318.zero N b
  neg := neg N b
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := sum_assoc N b
  zero_add := zero_sum N b
  add_zero := sum_zero N b
  neg_add_cancel := neg_sum N b
  add_comm := sum_comm N b

lemma neg_sum (p q:Points N b) :
    neg N b (sum N b p q)=sum N b (neg N b p) (neg N b q) := neg_add p q
lemma neg_triple (p:Points N b) :
    neg N b (sum N b (sum N b p p) p)=
      sum N b (sum N b (neg N b p) (neg N b p)) (neg N b p) := by
  rw [neg_sum,neg_sum]
end LiteralSchemePointGroup318
