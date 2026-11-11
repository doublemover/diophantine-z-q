module
public import IntegralDenominatorBaseDivisor318
public import FractionPolynomialFamilyLift318
public import FractionPrincipalCompatibility318
public import WholeFiniteFractionExtension318
public section
noncomputable section
namespace PrimitiveFractionNormalizationTransfer318
open Polynomial FractionFiniteCoefficientLift318 ActualPrincipalOpenRestriction318
variable (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Algebra R A] [FaithfulSMul R A]
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Transfer an ACTUAL localized chart element into any faithful whole
normalization with a specified primitive field generator. One produced
nonzero BASE denominator both inverts the old denominator and clears all
polynomial coefficients. The resulting equality holds inside the whole
original localization, not just its fraction field. -/
theorem exists_polynomial (b : A) (hb : b ≠ 0) (hi : IsIntegral R b)
    (a : Localization.Away b) (t : A)
    (ht : Function.Surjective
      (Polynomial.aeval (algebraMap A (FractionRing A) t) :
        Polynomial (FractionRing R) →ₐ[FractionRing R] FractionRing A)) :
    ∃ d : R, ∃ hd : d ≠ 0, ∃ hda : algebraMap R A d ≠ 0,
    ∃ hbd : b ∣ algebraMap R A d, ∃ H : Polynomial (Localization.Away d),
      H.eval₂ (Localization.awayMap (algebraMap R A) d)
        (algebraMap A (Localization.Away (algebraMap R A d)) t) =
          restriction b (algebraMap R A d) hbd a ∧
      (toField A (FractionRing A) (algebraMap R A d) hda)
        (H.eval₂ (Localization.awayMap (algebraMap R A) d)
          (algebraMap A (Localization.Away (algebraMap R A d)) t)) =
            toField A (FractionRing A) b hb a := by
  obtain ⟨c,hc,hbc⟩ := IntegralDenominatorBaseDivisor318.exists_divisor R A b hb hi
  obtain ⟨P,hP⟩ := ht (toField A (FractionRing A) b hb a)
  obtain ⟨p,hp,F,hF⟩ := FractionPolynomialFamilyLift318.exists_lift R (FractionRing R)
    (fun _ : Fin 1 => P)
  let d := p*c
  have hd : d ≠ 0 := mul_ne_zero hp hc
  have hda : algebraMap R A d ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R A).ne hd
  have hpd : p ∣ d := dvd_mul_right p c
  have hcd : c ∣ d := dvd_mul_left c p
  have hbd : b ∣ algebraMap R A d := hbc.trans (map_dvd (algebraMap R A) hcd)
  let H := (F 0).map (restriction p d hpd)
  let κ : FractionRing R →+* FractionRing A := algebraMap (FractionRing R) (FractionRing A)
  let φ := toField A (FractionRing A) (algebraMap R A d) hda
  let g := Localization.awayMap (algebraMap R A) d
  have hsquare : φ.comp g = κ.comp (toField R (FractionRing R) d hd) :=
    FractionPrincipalCompatibility318.base_field R A (FractionRing R) (FractionRing A)
      (algebraMap R A) κ
      (fun r => (IsScalarTower.algebraMap_apply R (FractionRing R) (FractionRing A) r).trans
        (IsScalarTower.algebraMap_apply R A (FractionRing A) r).symm) d hd hda
  have hH : H.map (toField R (FractionRing R) d hd) = P := by
    rw [H,Polynomial.map_map,FractionPrincipalCompatibility318.restriction_field R (FractionRing R) p d hp hd hpd]
    exact hF 0
  have hfield : φ (H.eval₂ g (algebraMap A (Localization.Away (algebraMap R A d)) t)) =
      toField A (FractionRing A) b hb a := by
    rw [Polynomial.hom_eval₂,hsquare,toField_coefficient,←Polynomial.eval₂_map,hH]
    exact hP
  refine ⟨d,hd,hda,hbd,H,?_,hfield⟩
  apply toField_injective A (FractionRing A) (algebraMap R A d) hda
  rw [hfield]
  have hr := FractionPrincipalCompatibility318.restriction_field A (FractionRing A)
    b (algebraMap R A d) hb hda hbd
  exact (congrArg (fun f : Localization.Away b →+* FractionRing A => f a) hr).symm
end PrimitiveFractionNormalizationTransfer318
