module
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic
public section
namespace SeparatedContactPivot318
variable {V : Type*} [CommRing V] [IsLocalRing V]
/-- At a point of a local ring, pairwise unit-separated contacts leave at
most one nonunit contact difference. The pivot is produced, not assumed. -/
theorem exists_pivot {ι : Type*} [Nonempty ι] (a : ι → V) (T : V)
    (hsep : ∀ i j,i≠j→IsUnit (a i-a j)) :
    ∃ i,∀ j,j≠i→IsUnit (T-a j) := by
  classical
  by_cases h : ∀ i,IsUnit (T-a i)
  · exact ⟨Classical.arbitrary ι,fun j _ => h j⟩
  · push_neg at h
    obtain ⟨i,hi⟩ := h
    refine ⟨i,?_⟩
    intro j hj
    by_contra hju
    have hneg : ¬IsUnit (-(T-a i)) := by simpa only [isUnit_neg] using hi
    have hh := IsLocalRing.nonunits_add hju hneg
    have he : (T-a j)+(-(T-a i))=a i-a j := by ring
    exact hh (he.symm ▸ hsep i j hj.symm)
end SeparatedContactPivot318
