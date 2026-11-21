module
public import ActualMulAffineFormallyEtale318
public import Mathlib.RingTheory.FinitePresentation
public section
noncomputable section

namespace ActualMulAffineEtale318
open AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 ActualNonSplitIdentityLifts318
open ActualMulAffineFormallyEtale318

/-- An actual affine chart restriction is étale. Relative finite
presentation is derived from the two genuine smooth affine charts over
the same R₀, not supplied as an additional hypothesis. This does not
select an affine cover of the entire multiplication morphism. -/
theorem exists_etale_mul_restriction (n : ℕ) {A B : Type} [CommRing A] [CommRing B]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ Curve n) [IsOpenImmersion j]
    (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
    (m : ℕ) (hm : IsUnit (m : OpenJModel318.Base n)) (hmem : Set.range (i ≫ mulMap n m) ⊆ Set.range j) :
    ∃ k : B →ₐ[OpenJModel318.Base n] A, (i ≫ mulMap n m = specOf n k ≫ j) ∧ Etale (specOf n k) := by
  obtain ⟨k, hk, he⟩ := exists_formallyEtale_mul_restriction n i j hi hj m hm hmem
  letI : Algebra B A := k.toRingHom.toAlgebra
  letI : IsScalarTower (OpenJModel318.Base n) B A := IsScalarTower.of_algHom k
  letI : Algebra.Smooth (OpenJModel318.Base n) A := chart_smooth n i hi
  letI : Algebra.Smooth (OpenJModel318.Base n) B := chart_smooth n j hj
  letI : Algebra.FinitePresentation B A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation (OpenJModel318.Base n) B A
  have hEtale : Algebra.Etale B A := ⟨he, inferInstance⟩
  refine ⟨k, hk, ?_⟩
  change Etale (Spec.algebraMap B A)
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap B A))).mpr (RingHom.etale_algebraMap.mpr hEtale)

end ActualMulAffineEtale318
