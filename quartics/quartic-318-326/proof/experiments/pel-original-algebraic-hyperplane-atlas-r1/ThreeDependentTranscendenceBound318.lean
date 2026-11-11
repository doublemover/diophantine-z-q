module
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.Basic
public section
noncomputable section
namespace ThreeDependentTranscendenceBound318
open scoped Cardinal
/-- Genuine transcendence-degree bound from dependence of EVERY triple.
The proof extracts three members from any larger independent subset;
no finite-generation, dimension, or geometric premise is inserted. -/
theorem trdeg_le_two {A:Type}[CommRing A][Algebra ℂ A]
    (h:∀z:Fin 3→A,¬AlgebraicIndependent ℂ z):Algebra.trdeg ℂ A≤2:=by
  rw [Algebra.trdeg]
  apply ciSup_le'
  intro s
  by_contra hn
  have ht:(2:Cardinal)<Cardinal.mk s.val:=lt_of_not_ge hn
  have h3:Cardinal.mk (Fin 3)≤Cardinal.mk s.val:=by
    simpa using (Cardinal.natCast_add_one_le_iff (n:=2)).mpr ht
  obtain ⟨e⟩:Nonempty (Fin 3↪s.val):=(Cardinal.le_def (Fin 3) s.val).mp h3
  exact h (fun i=>(e i).val) (s.property.comp e e.injective)
end ThreeDependentTranscendenceBound318
