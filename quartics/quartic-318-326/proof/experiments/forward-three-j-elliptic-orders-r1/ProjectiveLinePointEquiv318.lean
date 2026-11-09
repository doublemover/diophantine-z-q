module
public import ProjectiveLineFieldPoints318
public import Mathlib.Topology.Compactification.OnePoint.Basic
public section
noncomputable section
namespace ProjectiveLinePointEquiv318
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open ProjectiveLineFieldPoints318
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- Exact full overlap of the two original algebraic charts over any base. -/
lemma chart_zero_preimage_one :
    JLineAtlas318.chart R 0 ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=
      PrimeSpectrum.basicOpen (Polynomial.X:Polynomial R) := by
  rw [JLineAtlas318.chart_range]
  unfold JLineAtlas318.chart
  rw [Scheme.Hom.comp_preimage]
  erw [Proj.awayι_preimage_basicOpen (𝒜:=ProjectiveJLine318.grading R)
    (isHomogeneous_X R (0:Fin 2)) (by omega)
    (isHomogeneous_X R (1:Fin 2)) (by omega)]
  change PrimeSpectrum.basicOpen ((JLineAtlas318.chartEquiv R 0)
    (Away.isLocalizationElem (isHomogeneous_X R (0:Fin 2))
      (isHomogeneous_X R (1:Fin 2))))=_
  have h : Away.isLocalizationElem (isHomogeneous_X R (0:Fin 2))
      (isHomogeneous_X R (1:Fin 2))=
      (JLineAtlas318.chartEquiv R 0).symm Polynomial.X := by
    rw [JLineAtlas318.chartEquiv_symm_X]
    simp only [Away.isLocalizationElem,pow_one,ProjectiveChart318.coordinate]
    rfl
  rw [h,AlgEquiv.apply_symm_apply]

lemma infinity_preimage_finite :
    (chartPoint (R:=R) 0 (0:K)).val ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange=⊥ := by
  change (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) (0:K)).toRingHom) ≫
    JLineAtlas318.chart R 0) ⁻¹ᵁ _=⊥
  rw [Scheme.Hom.comp_preimage,chart_zero_preimage_one,SpecMap_preimage_basicOpen]
  simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,
    PrimeSpectrum.basicOpen_zero]

lemma finite_ne_infinity (t : K) :
    chartPoint (R:=R) 1 t ≠ chartPoint (R:=R) 0 (0:K) := by
  intro h
  have hp : (default : Spec (CommRingCat.of K)) ∈
      (chartPoint (R:=R) 0 (0:K)).val ⁻¹ᵁ (JLineAtlas318.chart R 1).opensRange := by
    rw [←h]
    exact ⟨Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=R) t).toRingHom) default,rfl⟩
  rw [infinity_preimage_finite] at hp
  exact hp

/-- Every original scheme-valued point is finite or the actual infinity point. -/
theorem finite_or_infinity (p : Points (R:=R) (K:=K)) :
    (∃ t : K, chartPoint (R:=R) 1 t=p) ∨ p=chartPoint (R:=R) 0 (0:K) := by
  obtain ⟨j,t,ht⟩ := every_point_in_chart p
  fin_cases j
  · by_cases hz : t=0
    · right
      simpa only [hz] using ht.symm
    · left
      refine ⟨t⁻¹,?_⟩
      have h : chartPoint (R:=R) 1 t⁻¹=chartPoint (R:=R) 0 t := by
        simpa only [Units.val_inv_eq_inv_val,Units.val_mk0,inv_inv] using
          unit_overlap (R:=R) (Units.mk0 t hz)⁻¹
      exact h.trans ht
  · exact Or.inl ⟨t,ht⟩

/-- Evaluation of the independently given one-point parameter in the original
homogeneous projective scheme. No topology is asserted at this stage. -/
@[expose] def pointMap (z : OnePoint K) : Points (R:=R) (K:=K) :=
  z.elim (chartPoint (R:=R) 0 (0:K)) (chartPoint (R:=R) 1)

lemma pointMap_bijective : Function.Bijective (pointMap (R:=R) (K:=K)) := by
  constructor
  · intro p q h
    induction p using OnePoint.rec with
    | infty =>
      induction q using OnePoint.rec with
      | infty => rfl
      | coe t => exact (finite_ne_infinity t h.symm).elim
    | coe s =>
      induction q using OnePoint.rec with
      | infty => exact (finite_ne_infinity s h).elim
      | coe t => exact congrArg ((↑) : K → OnePoint K) (chartPoint_injective 1 h)
  · intro p
    rcases finite_or_infinity p with ⟨t,ht⟩ | ht
    · exact ⟨(t:OnePoint K),ht⟩
    · exact ⟨OnePoint.infty,ht.symm⟩

@[expose] def pointEquiv : OnePoint K ≃ Points (R:=R) (K:=K) :=
  Equiv.ofBijective pointMap pointMap_bijective

lemma pointEquiv_finite (t : K) : pointEquiv (R:=R) (t:OnePoint K)=chartPoint (R:=R) 1 t := rfl
lemma pointEquiv_infinity : pointEquiv (R:=R) (OnePoint.infty : OnePoint K)=
    chartPoint (R:=R) 0 (0:K) := rfl

end ProjectiveLinePointEquiv318
