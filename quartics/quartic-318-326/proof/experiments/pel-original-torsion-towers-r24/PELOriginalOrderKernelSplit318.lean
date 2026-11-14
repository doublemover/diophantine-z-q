module
public import FiniteComplexPointIndex318
public import PELOriginalEtaleOrderIsogeny318
public import PELOriginalOrderKernelComplexPoints318
public section
noncomputable section
namespace PELOriginalOrderKernelSplit318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELOriginalOrderIntegralNorm318 PELOriginalOrderKernelScheme318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (ha : norm a≠0)
include ha in
lemma finiteMap : IsFinite (structureMap τ hτ a) :=
  (PELOriginalEtaleOrderIsogeny318.kernel_finite_etale τ hτ a ha).1
include ha in
lemma etaleMap : Etale (structureMap τ hτ a) :=
  (PELOriginalEtaleOrderIsogeny318.kernel_finite_etale τ hτ a ha).2
include ha in
lemma pointFinite : Finite (FiniteComplexPointsScheme318.Points (structureMap τ hτ a)) := by
  apply Nat.finite_of_card_ne_zero
  change Nat.card (KernelPoint τ hτ a (𝟙 (Spec (CommRingCat.of ℂ))))≠0
  rw [PELOriginalOrderKernelComplexPoints318.cardinality τ hτ a ha]
  exact pow_ne_zero _ (by simpa only [Int.natAbs_eq_zero] using ha)
local instance : Algebra ℂ Γ(Kernel τ hτ a,⊤) :=
  FiniteEtaleComplexSections318.algebra (structureMap τ hτ a)

include ha in
lemma reduced : AlgebraicGeometry.IsReduced (Kernel τ hτ a) := by
  letI := finiteMap τ hτ a ha
  letI := etaleMap τ hτ a ha
  exact FiniteEtaleComplexSections318.reduced (structureMap τ hτ a)

/-- The full original order-kernel global algebra splits using the
actual complex points of the SAME zero-fiber scheme. -/
@[expose] def split : Γ(Kernel τ hτ a,⊤) ≃ₐ[ℂ]
    (KernelPoint τ hτ a (𝟙 (Spec (CommRingCat.of ℂ)))→ℂ) := by
  letI := finiteMap τ hτ a ha
  letI := etaleMap τ hτ a ha
  letI := pointFinite τ hτ a ha
  exact FiniteComplexPointIndex318.split (structureMap τ hτ a)

@[expose] def schemeSplit : Kernel τ hτ a ≅
    Spec (CommRingCat.of (KernelPoint τ hτ a (𝟙 (Spec (CommRingCat.of ℂ)))→ℂ)) := by
  letI := finiteMap τ hτ a ha
  exact FiniteEtaleComplexSections318.schemeIso (structureMap τ hτ a) (split τ hτ a ha)
lemma schemeSplit_over : (schemeSplit τ hτ a ha).hom≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ
      (KernelPoint τ hτ a (𝟙 (Spec (CommRingCat.of ℂ)))→ℂ)))=structureMap τ hτ a := by
  letI := finiteMap τ hτ a ha
  exact FiniteEtaleComplexSections318.schemeIso_over _ _

include ha in
/-- Scheme-theoretic length is the square of the actual integral
reduced norm, after finite étale splitting and the full lattice-index count. -/
lemma length : Module.finrank ℂ Γ(Kernel τ hτ a,⊤)=(norm a).natAbs^2 := by
  letI := finiteMap τ hτ a ha
  letI := etaleMap τ hτ a ha
  letI := pointFinite τ hτ a ha
  rw [FiniteComplexPointIndex318.finrank]
  exact PELOriginalOrderKernelComplexPoints318.cardinality τ hτ a ha
end PELOriginalOrderKernelSplit318
