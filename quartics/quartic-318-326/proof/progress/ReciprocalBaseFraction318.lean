module
public import ReciprocalRatFunc318
public import ReciprocalInfinityNormalization318
public section
noncomputable section
namespace ReciprocalBaseFraction318
open Polynomial
open ReciprocalInfinityBase318
abbrev K := RatFunc ℚ
abbrev Base := ReciprocalOpen
abbrev L := InfinityFieldCoordinates318.L
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (L c) := (KummerTensorField318.source_raw_field c).toField
/-- The genuine reciprocal base maps into the original Q(t) by s ↦ 1/t. -/
@[expose] def baseFieldMap : Base c →+* K :=
  IsLocalization.Away.lift (reciprocalDenominator c)
    (S:=Base c) (g:=(Polynomial.aeval ((RatFunc.X : K)⁻¹)).toRingHom)
    (IsUnit.mk0 _ (by
      intro h
      apply reciprocalDenominator_ne_zero c
      apply ReciprocalRatFunc318.inverse_aeval_injective
      simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_zero] using h))
lemma on_polynomial (p : ℚ[X]) :
    baseFieldMap c (algebraMap ℚ[X] (Base c) p) =
      Polynomial.aeval ((RatFunc.X : K)⁻¹) p :=
  IsLocalization.Away.lift_eq _ _ _
lemma on_coordinate : baseFieldMap c (algebraMap ℚ[X] (Base c) X) =
    (RatFunc.X : K)⁻¹ := by rw [on_polynomial, Polynomial.aeval_X]
@[expose, instance_reducible] def baseAlgebra : Algebra (Base c) K := (baseFieldMap c).toAlgebra
/-- Fraction-ring structure uses the actual reciprocal map, not the usual
polynomial t-coordinate embedding. -/
lemma actual_fractionField :
    letI : Algebra (Base c) K := baseAlgebra c
    IsFractionRing (Base c) K := by
  letI : Algebra ℚ[X] K := (Polynomial.aeval ((RatFunc.X : K)⁻¹)).toRingHom.toAlgebra
  letI : Algebra (Base c) K := baseAlgebra c
  letI : SMul ℚ[X] K := (inferInstance : Algebra ℚ[X] K).toSMul
  letI : SMul (Base c) K := (baseAlgebra c).toSMul
  letI : Module ℚ[X] K := Algebra.toModule
  letI : Module (Base c) K := Algebra.toModule
  letI : IsFractionRing ℚ[X] K := ReciprocalRatFunc318.inverse_fractionRing
  letI : IsScalarTower ℚ[X] (Base c) K :=
    IsScalarTower.of_algebraMap_eq (R:=ℚ[X]) (S:=Base c) (A:=K) (fun p => (on_polynomial c p).symm)
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (reciprocalDenominator c)) (Base c) K
/-- Exact original-field square, on the entire reciprocal localized ring. -/
lemma original_field_square :
    (algebraMap K (L c)).comp (baseFieldMap c) =
      ReciprocalInfinityNormalization318.reciprocalEmbedding c := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (reciprocalDenominator c))
  apply Polynomial.ringHom_ext
  · intro q
    change algebraMap K (L c) (baseFieldMap c (algebraMap ℚ (Base c) q)) =
      ReciprocalInfinityNormalization318.reciprocalEmbedding c (algebraMap ℚ (Base c) q)
    rw [RingHom.map_rat_algebraMap,RingHom.map_rat_algebraMap,RingHom.map_rat_algebraMap]
  · change algebraMap K (L c) (baseFieldMap c (algebraMap ℚ[X] (Base c) X)) = _
    rw [on_coordinate,map_inv₀,RingHom.comp_apply,ReciprocalInfinityNormalization318.reciprocalEmbedding_coordinate]
    rfl
lemma original_field_value (x : Base c) :
    algebraMap K (L c) (baseFieldMap c x) =
      ReciprocalInfinityNormalization318.reciprocalEmbedding c x :=
  RingHom.congr_fun (original_field_square c) x
end ReciprocalBaseFraction318
