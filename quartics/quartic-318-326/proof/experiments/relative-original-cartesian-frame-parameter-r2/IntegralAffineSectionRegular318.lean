module
public import IntegralLineRestriction318
public import OriginalAffineOpenFrame318
public import OriginalSectionPullbackComposition318
public import SectionZeroRegularCoordinate318
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace IntegralAffineSectionRegular318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u

/-- On the actual affine line module, flatness over a domain makes any
nonzero section intrinsically regular. No choice of global frame. -/
lemma affine (A : CommRingCat.{u}) [IsDomain A] (L : Line (Spec A))
    (s : OriginalLineAffineModel318.sections A L) (hs : s≠0) :
    Function.Injective (SectionZeroRegularCoordinate318.sectionMap A
      (OriginalLineAffineModel318.sections A L) s) := by
  letI := (OriginalLineAffineModel318.properties A L).2.1
  intro a b hab
  by_contra hn
  have hne : a-b≠0 := sub_ne_zero.mpr hn
  have hz : (a-b) • s = (a-b) • (0 : OriginalLineAffineModel318.sections A L) := by
    change a • s=b • s at hab
    simp only [sub_smul,hab,sub_self,smul_zero]
  exact hs (Module.Flat.isSMulRegular_of_nonZeroDivisors
    (M:=OriginalLineAffineModel318.sections A L)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hne) hz)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] (A : CommRingCat.{u})
  (j : Spec A ⟶ X) [IsOpenImmersion j] (L : Line X)
  (s : Γ(L.object,⊤)) (hs : s≠0)
local notation "N" => LineSheafPullback318.line j L

/-- A nonzero global section on the SAME integral scheme is regular on
every actual affine open, including the empty one. Pullback is the original
adjunction unit and is compared with actual whole-open restriction. -/
lemma open_pull : Function.Injective (SectionZeroRegularCoordinate318.sectionMap A
    (OriginalLineAffineModel318.sections A N)
    (OriginalSectionPullbackComposition318.pull j L.object s)) := by
  classical
  let U := j ''ᵁ ⊤
  let e := OriginalAffineOpenFrame318.ringEquivalence A j
  by_cases hn : Nonempty U
  · letI := hn
    letI : IsDomain A := Function.Injective.isDomain e.symm.toRingHom e.symm.injective
    apply affine A N
    intro hz
    apply hs
    apply IntegralLineRestriction318.zero_of_restrict_zero L U s
    have h := OriginalOpenPullbackSections318.unit_sections j L.object s
    have hp : OriginalOpenPullbackSections318.sectionPull j L.object s=0 := hz
    rw [hp,map_zero] at h
    exact h.symm
  · have hbot : U=⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (hn ⟨⟨x,hx⟩⟩).elim
    haveI : Subsingleton Γ(X,U) := by rw [hbot]; infer_instance
    intro a b _
    exact e.symm.injective (Subsingleton.elim _ _)
end IntegralAffineSectionRegular318
