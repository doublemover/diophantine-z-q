module
public import FiniteFlatFiberPointBound318
public import FiniteFamilyAvoidanceOpen318
public import Mathlib.Tactic
public section
noncomputable section
namespace BoundedFiniteFamilyAvoidance318
open AlgebraicGeometry CategoryTheory
open FiniteFamilyAvoidanceOpen318
universe u
variable {Z B X : Scheme.{u}} (p : Z ⟶ B) [IsFinite p] [Flat p] (q : Z ⟶ X)
  (N : ℕ) (U : Fin (N+1) → X.Opens)
  (hU : ∀ i j, i≠j → U i⊔U j=⊤)
  (hN : ∀ b : B,p.finrank b≤N)
/-- Among N+1 pairwise disjoint excluded source fibers, some source open
contains the ENTIRE original degree-at-most-N fiber. -/
lemma exists_avoiding (b : B) : ∃ i, b∈locus p q (U i) := by
  classical
  by_contra h
  have bad (i : Fin (N+1)) : ∃ z : Z, p z=b ∧ q z∉U i := by
    have hi : ¬∀ z : Z,p z=b → q z∈U i := by
      intro hi
      exact h ⟨i,(mem_locus p q (U i) b).mpr hi⟩
    simpa only [not_forall,not_imp] using hi
  choose z hz hbad using bad
  let w : Fin (N+1) → p ⁻¹' {b} := fun i => ⟨z i,hz i⟩
  have hinj : Function.Injective w := by
    intro i j hij
    by_contra hne
    have he : z i=z j := congrArg Subtype.val hij
    have hp : q (z i)∈U i⊔U j := by rw [hU i j hne]; trivial
    rcases hp with hi | hj
    · exact hbad i hi
    · exact hbad j (he ▸ hj)
  letI : Fintype (p ⁻¹' {b}) := Fintype.ofFinite _
  have hc : N+1≤Nat.card (p ⁻¹' {b}) := by
    simpa only [Fintype.card_fin,Nat.card_eq_fintype_card] using Fintype.card_le_of_injective w hinj
  have hb := (FiniteFlatFiberPointBound318.card_le_rank p b).trans (hN b)
  omega
lemma cover : (⨆ i, locus p q (U i))=⊤ := by
  ext b
  exact iff_true_intro (TopologicalSpace.Opens.mem_iSup.mpr (exists_avoiding p q N U hU hN b))
end BoundedFiniteFamilyAvoidance318
