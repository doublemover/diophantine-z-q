module
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace ReciprocalRatFunc318
open Polynomial
attribute [-instance] DivisionRing.toRatAlgebra
abbrev K := RatFunc ℚ
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma inverse_transcendental : Transcendental ℚ ((RatFunc.X : K)⁻¹) := by
  intro h
  exact (RatFunc.transcendental_X (K:=ℚ)) (by simpa only [inv_inv] using h.inv)
lemma inverse_aeval_injective : Function.Injective (Polynomial.aeval ((RatFunc.X : K)⁻¹) : ℚ[X] →ₐ[ℚ] K) :=
  transcendental_iff_injective.mp inverse_transcendental
/-- The actual rational-coordinate inversion t ↦ 1/t. -/
@[expose] def inversionHom : K →ₐ[ℚ] K :=
  RatFunc.liftAlgHom (Polynomial.aeval ((RatFunc.X : K)⁻¹))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ inverse_aeval_injective)
lemma on_polynomial (p : ℚ[X]) :
    inversionHom (algebraMap ℚ[X] K p) = Polynomial.aeval ((RatFunc.X : K)⁻¹) p :=
  RatFunc.liftRingHom_algebraMap _ _ _
lemma on_X : inversionHom RatFunc.X = (RatFunc.X : K)⁻¹ := by
  simpa only [RatFunc.algebraMap_X,Polynomial.aeval_X] using on_polynomial X
lemma twice (x : K) : inversionHom (inversionHom x) = x := by
  have hp : (inversionHom.toRingHom.comp inversionHom.toRingHom).comp (algebraMap ℚ[X] K) =
      algebraMap ℚ[X] K := by
    apply Polynomial.ringHom_ext
    · intro q
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        RatFunc.algebraMap_C,←RatFunc.algebraMap_eq_C,AlgHom.commutes]
    · simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        RatFunc.algebraMap_X,on_X,map_inv₀,inv_inv]
  have he : inversionHom.toRingHom.comp inversionHom.toRingHom = RingHom.id K :=
    IsFractionRing.ringHom_ext (A:=ℚ[X]) (fun p => congrArg (fun h : ℚ[X] →+* K => h p) hp)
  exact congrArg (fun h : K →+* K => h x) he
@[expose] def inversion : K ≃+* K :=
  { inversionHom.toRingHom with
    invFun := inversionHom
    left_inv := twice
    right_inv := twice }
/-- Q(t) is the fraction field of the reciprocal polynomial map, not just
of the usual t-coordinate map. -/
lemma inverse_fractionRing :
    letI : Algebra ℚ[X] K := (Polynomial.aeval ((RatFunc.X : K)⁻¹)).toRingHom.toAlgebra
    IsFractionRing ℚ[X] K := by
  have he : inversion.toRingHom.comp (algebraMap ℚ[X] K) =
      (Polynomial.aeval ((RatFunc.X : K)⁻¹)).toRingHom :=
    RingHom.ext on_polynomial
  have hh := (IsLocalization.isLocalization_iff_of_ringEquiv
    (nonZeroDivisors ℚ[X]) inversion).mp (inferInstance : IsFractionRing ℚ[X] K)
  rw [← he]
  exact hh
end ReciprocalRatFunc318
