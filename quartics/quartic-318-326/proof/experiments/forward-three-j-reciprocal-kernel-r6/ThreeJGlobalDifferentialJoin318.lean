module
public import ThreeJLocalAnnihilators318
public section
noncomputable section
namespace ThreeJGlobalDifferentialJoin318
open AlgebraicGeometry Polynomial
open ThreeJGlobalRamificationScheme318 ThreeJGlobalKernelChart318
open ThreeJCuspDifferentialCharts318 ThreeProjectiveJCertificates318
open ThreeJRamificationIdealCharts318 ThreeJRelativeDifferentials318
open LocalizedRationalDifferentials318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual affine-coordinate ideal of the restriction of the global
closed ramification kernel. This is not defined by its proposed equation. -/
@[expose] def finiteCoordinateIdeal : Ideal ℚ[X] :=
  ((ideal.comap (JLineAtlas318.chart ℚ 1)).ideal
    ⟨⊤,isAffineOpen_top (Spec (CommRingCat.of ℚ[X]))⟩).comap
      (Scheme.ΓSpecIso (CommRingCat.of ℚ[X])).inv.hom

theorem finiteCoordinateIdeal_eq : finiteCoordinateIdeal=Ideal.span {finiteEquation} :=
  finite_equation

/-- Extension of the actual restricted global ideal to the entire
original Laurent ring is exactly the literal differential annihilator. -/
theorem laurent_ideal :
    Ideal.map (algebraMap ℚ[X] ThreeJLaurentEquiv318.Laurent) finiteCoordinateIdeal =
      originalDifferentialIdeal := by
  rw [finiteCoordinateIdeal_eq,Ideal.map_span,Set.image_singleton]
  have hp : finiteNumerator.derivative*finiteDenominator-
      finiteNumerator*finiteDenominator.derivative=finiteEquation := by
    unfold finiteEquation
    linear_combination -finite_wronskian
  have h := ThreeJLaurentDifferentialJoin318.literal_coefficient_ideal
  rw [hp] at h
  have hs : IsUnit ProjectiveLineOverlap318.s :=
    IsUnit.of_mul_eq_one_right _ ProjectiveLineOverlap318.ts
  rw [Ideal.span_singleton_mul_right_unit ((hs.pow 3).pow 2)] at h
  exact h

/-- Exact global-kernel/differential comparison on the finite cusp
localization, including its original double ramification component. -/
theorem finite_cusp_join (a : FiniteRing) :
    letI := targetAlgebra finiteDenominator finiteNumerator finiteInverse
    (∀ w : KaehlerDifferential ℚ[X] FiniteRing, a • w=0) ↔
      a ∈ Ideal.map (value finiteNumerator).toRingHom finiteCoordinateIdeal := by
  letI := targetAlgebra finiteDenominator finiteNumerator finiteInverse
  rw [finiteCoordinateIdeal_eq]
  exact ThreeJLocalAnnihilators318.finite_annihilator a

/-- Exact global-kernel/differential comparison on the actual Laurent
source and under the original j scalar action. -/
theorem laurent_join (a : ThreeJLaurentEquiv318.Laurent) :
    letI := ThreeJFiniteLaurentMap318.jAlgebra
    (∀ w : KaehlerDifferential ThreeJMonicAlgebra318.Base ThreeJLaurentEquiv318.Laurent,
      a • w=0) ↔
      a ∈ Ideal.map (algebraMap ℚ[X] ThreeJLaurentEquiv318.Laurent) finiteCoordinateIdeal := by
  letI := ThreeJFiniteLaurentMap318.jAlgebra
  rw [laurent_ideal]
  exact ThreeJLocalAnnihilators318.laurent_annihilator a

/-- The same actual global ideal has the original reciprocal principal
ideal on the complete Laurent intersection, retaining its degree-six unit
transition. This does not replace the still separate whole-chart restriction
comparison at the reciprocal source origin. -/
theorem reciprocal_overlap_join :
    Ideal.map (algebraMap ℚ[X] ProjectiveLineOverlap318.A) finiteCoordinateIdeal =
      Ideal.map (Polynomial.aeval (R:=ℚ) ProjectiveLineOverlap318.s).toRingHom
        (Ideal.span {infinityEquation}) := by
  rw [finiteCoordinateIdeal_eq]
  exact overlap_ideal
end ThreeJGlobalDifferentialJoin318
