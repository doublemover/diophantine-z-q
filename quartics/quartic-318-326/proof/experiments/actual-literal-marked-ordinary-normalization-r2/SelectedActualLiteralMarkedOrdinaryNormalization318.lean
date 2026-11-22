module

public import SelectedActualLiteralMarkedGenericTensor318
public import SelectedActualMonicOrdinaryNormalizationComparison318

public section
noncomputable section

open scoped Polynomial TensorProduct nonZeroDivisors
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedComplexGenericRatFunc318 SelectedActualComplexOrdinaryScalar318
open SelectedActualLiteralComplexCompactStalkDVR318 SelectedActualLiteralMarkedGenericTensor318
open SelectedActualMonicOrdinaryNormalizationComparison318
open SelectedActualComplexGenericChartClosures318

namespace SelectedActualLiteralMarkedOrdinaryNormalization318

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

abbrev B (F : Type*) [Field F] [Algebra JField F] :=
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  integralClosure ℂ[X] F

abbrev O (F : Type*) [Field F] [Algebra JField F] :=
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  Localization (Algebra.algebraMapSubmonoid (B F) (Submonoid.powers denominator))

private theorem mapped_derivative_is_unit (hd : IsUnit (AdjoinRoot.mk p p.derivative)) :
    IsUnit (AdjoinRoot.mk (pC N p) (pC N p).derivative) := by
  let f := toComplex N
  let q := pC N p
  let r : AdjoinRoot p →+* AdjoinRoot q := AdjoinRoot.map f p q (dvd_refl _)
  have hm : r.comp (AdjoinRoot.mk p) =
      (AdjoinRoot.mk q).comp (Polynomial.mapRingHom f) := by
    apply Polynomial.ringHom_ext
    · intro c
      change AdjoinRoot.map f p q (dvd_refl _) (AdjoinRoot.of p c) =
        AdjoinRoot.mk q ((Polynomial.C c).map f)
      rw [Polynomial.map_C,AdjoinRoot.map_of] <;> rfl
    · change AdjoinRoot.map f p q (dvd_refl _) (AdjoinRoot.root p) =
        AdjoinRoot.mk q (Polynomial.X.map f)
      rw [Polynomial.map_X,AdjoinRoot.map_root] <;> rfl
  have h := RingHom.congr_fun hm p.derivative
  change r (AdjoinRoot.mk p p.derivative) = AdjoinRoot.mk q (p.derivative.map f) at h
  rw [← Polynomial.derivative_map] at h
  exact Eq.mp (congrArg (fun y : AdjoinRoot q => IsUnit y) h) (hd.map r)

/-- In the *verified whole marked field*, compare the actual ordinary
original monic chart with the localization of its finite normal
chart, at the exact original ordinary denominator. The comparison
preserves the entire generic map, and hence the marked root itself. -/
theorem actual_literal_ordinary_normalization
    (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (hf : IsField (AdjoinRoot (P N p))) :
    letI : Field (K N p) := (whole_isField N p hf).toField
    let F := K N p
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    ∃ (q : O F →+* F) (e : C N p ≃ₐ[Base] O F),
      q.comp (algebraMap (B F) (O F)) = algebraMap (B F) F ∧
      ∀ z : C N p, q (e z) = literalWholeTensor N p (z ⊗ₜ[Base] (1 : Generic)) := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base (RatFunc ℂ) := ratscalar
  letI : IsScalarTower ℂ[X] Base (RatFunc ℂ) := rattower
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  letI : IsScalarTower ℂ[X] Base F := IsScalarTower.of_algebraMap_eq fun a => by
    change polynomial F 1 a =
      algebraMap (RatFunc ℂ) F (algebraMap Base (RatFunc ℂ) (algebraMap ℂ[X] Base a))
    have h₁ : basePolynomial 1 = algebraMap ℂ[X] (RatFunc ℂ) := by simp [basePolynomial]
    rw [← IsScalarTower.algebraMap_apply ℂ[X] Base (RatFunc ℂ),
      polynomial,RingHom.comp_apply,h₁]
  let dB : B F := algebraMap ℂ[X] (B F) denominator
  have hM : Algebra.algebraMapSubmonoid (B F) (Submonoid.powers denominator) =
      Submonoid.powers dB := by
    unfold Algebra.algebraMapSubmonoid
    exact Submonoid.map_powers _ _
  letI : IsLocalization.Away dB (O F) := hM ▸ (inferInstance :
    IsLocalization (Algebra.algebraMapSubmonoid (B F) (Submonoid.powers denominator)) (O F))
  have hdinj : Function.Injective (polynomial F 1) := by
    letI : Algebra ℂ[X] JField := (basePolynomial 1).toAlgebra
    letI : IsFractionRing ℂ[X] JField := base_fractionRing 1
    exact (algebraMap JField F).injective.comp (IsFractionRing.injective ℂ[X] JField)
  have hden : denominator ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (inversion_support (Submonoid.mem_powers _))
  have hv : IsUnit (algebraMap (B F) F dB) := by
    apply isUnit_iff_ne_zero.mpr
    change polynomial F 1 denominator ≠ 0
    intro hz
    exact hden (hdinj (hz.trans (map_zero (polynomial F 1)).symm))
  let q : O F →+* F := IsLocalization.Away.lift dB (g := algebraMap (B F) F) hv
  have hq (b : B F) : q (algebraMap (B F) (O F) b) = algebraMap (B F) F b :=
    IsLocalization.Away.lift_eq dB hv b
  letI : Algebra (O F) F := q.toAlgebra
  letI : IsScalarTower (B F) (O F) F :=
    IsScalarTower.of_algebraMap_eq fun b => (hq b).symm
  letI : IsScalarTower Base (O F) F := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (Submonoid.powers denominator)
    apply RingHom.ext
    intro a
    change algebraMap Base F (algebraMap ℂ[X] Base a) =
      algebraMap (O F) F (algebraMap Base (O F) (algebraMap ℂ[X] Base a))
    rw [← IsScalarTower.algebraMap_apply ℂ[X] Base F,
      ← IsScalarTower.algebraMap_apply ℂ[X] Base (O F),
      IsScalarTower.algebraMap_apply ℂ[X] (B F) (O F),
      ← IsScalarTower.algebraMap_apply (B F) (O F) F,
      ← IsScalarTower.algebraMap_apply ℂ[X] (B F) F]
  letI : IsDomain Base := coefficient_domain
  letI : IsIntegrallyClosed Base := coefficient_normal
  obtain ⟨e,he⟩ := ordinary_monic_compares_in_the_whole_field
    (B := B F) (O := O F) (Submonoid.powers denominator) (pC N p)
    (hp.map (toComplex N)) (mapped_derivative_is_unit N p hd) (literalWholeTensor N p)
  refine ⟨q,e,?_ ,he⟩
  exact RingHom.ext hq

end SelectedActualLiteralMarkedOrdinaryNormalization318

#print axioms SelectedActualLiteralMarkedOrdinaryNormalization318.actual_literal_ordinary_normalization
