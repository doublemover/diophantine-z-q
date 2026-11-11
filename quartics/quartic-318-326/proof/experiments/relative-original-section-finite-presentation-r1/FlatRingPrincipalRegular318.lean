module
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace FlatRingPrincipalRegular318
universe u
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [hflat : Module.Flat A B]
  (c : A) (hc : ∀ a : A,a*c=0 → a=0)
include hc hflat in
/-- A genuine nonzerodivisor remains one under flat ambient extension;
this is used only for actual flat open refinements, not for arbitrary
coefficient changes of a nonflat closed quotient. -/
lemma regular : ∀ b : B,b*algebraMap A B c=0 → b=0 := by
  have hn : c ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    exact hc a (by simpa only [mul_comm] using ha)
  intro b hb
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) hn
  change algebraMap A B c*b=algebraMap A B c*0
  simpa only [mul_comm,mul_zero] using hb
end FlatRingPrincipalRegular318
