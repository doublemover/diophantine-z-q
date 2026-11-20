module
public import SelectedPrimitiveXCharacteristic318
public import SelectedMonogenicNormalBasis318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.RingHom.Etale
public section
noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318

namespace SelectedPrimitivePowerBasis318

variable (M : ℕ)

private theorem denominator_ne_zero (hM : M ≠ 0) : OpenJModel318.denominator M ≠ 0 := by
  unfold OpenJModel318.denominator
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hM)
    · exact Polynomial.X_ne_zero
  · simpa using Polynomial.X_sub_C_ne_zero (1728 : ℤ)

theorem base_domain (hM : M ≠ 0) : IsDomain (R M) :=
  IsLocalization.Away.isDomain _ (denominator_ne_zero M hM)

theorem base_normal (hM : M ≠ 0) : IsIntegrallyClosed (R M) := by
  apply isIntegrallyClosed_of_isLocalization (R M) (Submonoid.powers (OpenJModel318.denominator M))
  rintro _ ⟨d,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero d (denominator_ne_zero M hM))

variable (I : Ideal (D M))
variable (τ : (D M ⧸ I) →ₐ[R M] (D M ⧸ I))
variable (hτ : τ.comp (q M I) = (q M I).comp (sign M))
variable (hinv : τ.comp τ = AlgHom.id (R M) (D M ⧸ I))

theorem coordinate_generates :
    Function.Surjective (aeval (coordinate M I τ hτ) :
      (R M)[X] →ₐ[R M] (fixed M I τ)) := by
  intro b
  obtain ⟨p,hp⟩ := (fixed_iff_polynomial M I τ hτ b.val).mp b.property
  refine ⟨p,Subtype.ext ?_⟩
  change (fixed M I τ).val (aeval (coordinate M I τ hτ) p) = b.val
  rw [← Polynomial.aeval_algHom_apply]
  exact hp

/-- This is the basis on the fixed coordinate ring of the same τ and the
same literal x. No geometric labeling or basis is a hypothesis. -/
theorem powers (hM : M ≠ 0) [Module.Finite (R M) (D M ⧸ I)]
    [Algebra.Etale (R M) (D M ⧸ I)] :
    ∃ pb : PowerBasis (R M) (fixed M I τ), pb.gen = coordinate M I τ hτ := by
  letI : IsDomain (R M) := base_domain M hM
  letI : IsIntegrallyClosed (R M) := base_normal M hM
  have h := (RingHom.Etale.iff_flat_and_formallyUnramified.mp
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale (R M) (D M ⧸ I)))).1
  letI : Module.Flat (R M) (D M ⧸ I) := RingHom.flat_algebraMap_iff.mp h
  obtain ⟨hfin,hflat⟩ := finite_flat_fixed M I τ hinv
  letI : Module.Finite (R M) (fixed M I τ) := hfin
  letI : Module.Flat (R M) (fixed M I τ) := hflat
  exact SelectedMonogenicNormalBasis318.exists_powers _ (coordinate_generates M I τ hτ)

/-- Instantiate the construction on the actual arbitrary-M primitive
Scheme and its original negation. Only the typed kernel hypotheses survive. -/
theorem actual_primitive_powers [IsFinite (kernelProjection M M)] [Etale (kernelProjection M M)]
    (hM : 2 < M) :
    ∃ (I : Ideal (D M)) (e : PrimitiveScheme M M ≅ Spec (CommRingCat.of (D M ⧸ I))),
      intoAffine M M (by omega) =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      ∃ (τ : (D M ⧸ I) →ₐ[R M] (D M ⧸ I))
        (hτ : τ.comp (q M I) = (q M I).comp (sign M)),
        τ.comp τ = AlgHom.id (R M) (D M ⧸ I) ∧
        ∃ pb : PowerBasis (R M) (fixed M I τ), pb.gen = coordinate M I τ hτ := by
  have hM₁ : 1 < M := by omega
  obtain ⟨I,e,he,_,hfin,het⟩ := affine_quotient M M hM₁
  obtain ⟨τ,hτ,hinv⟩ := quotient_sign M M hM₁ I e he
  letI : Module.Finite (R M) (D M ⧸ I) := hfin
  letI : Algebra.Etale (R M) (D M ⧸ I) := het
  exact ⟨I,e,he,τ,hτ,hinv,powers M I τ hτ hinv (by omega)⟩

end SelectedPrimitivePowerBasis318

#print axioms SelectedPrimitivePowerBasis318.actual_primitive_powers
