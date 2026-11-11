module
public import PolynomialNonzeroIdealFinite318
public import IntegralAffineSectionRegular318
public import OriginalAffineSectionZero318
public section
noncomputable section
namespace OriginalIntegralPolynomialZeroFinite318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (K : Type u) [Field K] (A : CommRingCat.{u})
  [Algebra K A] [Algebra (Polynomial K) A] [IsScalarTower K (Polynomial K) A]
  [Module.Finite (Polynomial K) A] [Module.Free (Polynomial K) A]

/-- A nonzero section of the ORIGINAL affine line has a nonzero actual
evaluation ideal. Its quotient is finite over the original field when
the chart is a finite free integral polynomial chart. -/
lemma affine [IsDomain A] (L : Line (Spec A))
    (s : OriginalLineAffineModel318.sections A L) (hs : s≠0) :
    Module.Finite K (A⧸OriginalAffineSectionZero318.ideal A L s) := by
  letI := (OriginalLineAffineModel318.properties A L).1
  have hI : OriginalAffineSectionZero318.ideal A L s≠⊥ := by
    intro h
    exact hs ((ProjectiveSectionIdeal318.ideal_eq_bot_iff A
      (OriginalLineAffineModel318.sections A L) s).mp h)
  exact PolynomialNonzeroIdealFinite318.finite K A _ hI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} [IsIntegral X] (j : Spec A ⟶ X) [IsOpenImmersion j]
  (L : Line X) (s : Γ(L.object,⊤)) (hs : s≠0)
local notation "N" => LineSheafPullback318.line j L
local notation "σ" => OriginalSectionPullbackComposition318.pull j L.object s

/-- Finite field quotient for the literal zero on EVERY actual whole
polynomial affine open of an integral source. Nonzero restriction is
proved, and the empty chart gives the zero quotient separately. -/
lemma open_pull : Module.Finite K (A⧸OriginalAffineSectionZero318.ideal A N σ) := by
  classical
  let U := j ''ᵁ ⊤
  let e := OriginalAffineOpenFrame318.ringEquivalence A j
  by_cases hn : Nonempty U
  · letI := hn
    letI : IsDomain A := Function.Injective.isDomain e.symm.toRingHom e.symm.injective
    apply affine K A N σ
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
    haveI : Subsingleton A := ⟨fun a b => e.symm.injective (Subsingleton.elim _ _)⟩
    infer_instance
end OriginalIntegralPolynomialZeroFinite318
