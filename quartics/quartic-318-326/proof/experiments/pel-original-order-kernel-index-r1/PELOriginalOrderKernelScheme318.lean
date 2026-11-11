module
public import PELOriginalOrderFppfDivision318
public section
noncomputable section
namespace PELOriginalOrderKernelScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PELPrincipalOrderCoordinates318
open PELOriginalProductChartCover318 PELOriginalSchemePointGroup318
open PELOriginalOrderSchemeMorphism318 PELOriginalOrderIntegralNorm318
open PELOriginalSchemeGroupUnitInverse318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
/-- The genuine whole scheme-theoretic zero fiber of the original order
endomorphism; no radical or reduced replacement is taken. -/
abbrev Kernel := pullback (morphism τ hτ a) (zeroPoint τ hτ)
@[expose] def inclusion : Kernel τ hτ a⟶PELOriginalReducedProjectiveCandidate318.candidate τ hτ :=
  pullback.fst _ _
@[expose] def structureMap : Kernel τ hτ a⟶Spec (CommRingCat.of ℂ) := pullback.snd _ _
lemma inclusion_over : inclusion τ hτ a≫π τ hτ=structureMap τ hτ a := by
  have h := congrArg (fun k => k≫π τ hτ)
    (pullback.condition (f := morphism τ hτ a) (g := zeroPoint τ hτ))
  simpa only [Category.assoc,over_complex,zero_over,Category.comp_id] using h
variable {T : Scheme} (ρ : T⟶Spec (CommRingCat.of ℂ))
abbrev KernelPoint := {p : T⟶Kernel τ hτ a // p≫structureMap τ hτ a=ρ}
abbrev PointKernel := (PELOriginalUniversalOrderAction318.endomorphism τ hτ ρ a).ker
@[expose] def toPoint (p : KernelPoint τ hτ a ρ) : PointKernel τ hτ a ρ :=
  ⟨⟨p.val≫inclusion τ hτ a,by rw [Category.assoc,inclusion_over]; exact p.property⟩,by
    apply Subtype.ext
    change (p.val≫inclusion τ hτ a)≫morphism τ hτ a=ρ≫zeroPoint τ hτ
    rw [Category.assoc]
    change p.val≫(pullback.fst _ _≫morphism τ hτ a)=_
    rw [pullback.condition,←Category.assoc]
    exact congrArg (fun k => k≫zeroPoint τ hτ) p.property⟩
@[expose] def fromPoint (p : PointKernel τ hτ a ρ) : KernelPoint τ hτ a ρ :=
  ⟨pullback.lift p.val.val ρ (by
    have h := congrArg Subtype.val p.property
    exact h),pullback.lift_snd _ _ _⟩
/-- Both-inverse representation of the actual additive kernel on EVERY
scheme test, including nilpotents and arbitrary non-finite-type tests. -/
@[expose] def equivalence : KernelPoint τ hτ a ρ ≃ PointKernel τ hτ a ρ where
  toFun := toPoint τ hτ a ρ
  invFun := fromPoint τ hτ a ρ
  left_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans p.property.symm
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
lemma finite_smooth (ha : norm a≠0) :
    IsFinite (structureMap τ hτ a) ∧ Smooth (structureMap τ hτ a) := by
  letI := PELOriginalFiniteOrderIsogeny318.finite τ hτ a ha
  letI := PELOriginalSmoothOrderIsogeny318.smooth τ hτ a ha
  exact ⟨inferInstanceAs (IsFinite (pullback.snd (morphism τ hτ a) (zeroPoint τ hτ))),
    inferInstanceAs (Smooth (pullback.snd (morphism τ hτ a) (zeroPoint τ hτ)))⟩
end PELOriginalOrderKernelScheme318
