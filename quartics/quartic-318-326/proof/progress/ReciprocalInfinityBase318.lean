module
public import InfinityNormalChart318
public import LinearRootCoordinate318
public import Mathlib.RingTheory.RingHom.Finite
public section
noncomputable section
namespace ReciprocalInfinityBase318
open Polynomial
open InfinityOpenChart318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)

/-- The reciprocal projective coordinate s=1/t, written in the ramified
root coordinate u: s=u²/c₀. -/
@[expose] def substitution : R→+*R :=
  (LinearRootCoordinate318.baseSubstitution (c 0) (0:ℚ)).toRingHom
@[expose] def linearCoefficient (j:Fin 3) : R :=
  C ((c j.succ:ℚ)/(c 0:ℚ))*(1-C (InfinityParameters318.contact j)*X)
@[expose] def reciprocalDenominator : R := ∏j:Fin 3,linearCoefficient c j
abbrev ReciprocalOpen:=Localization.Away (reciprocalDenominator c)

theorem substitution_X : substitution c X=C (↑((c 0)⁻¹):ℚ)*X^2 := by
  simp [substitution,LinearRootCoordinate318.baseSubstitution]

theorem substitution_coefficient (j:Fin 3) :
    substitution c (linearCoefficient c j)=InfinityParameters318.coefficient c j := by
  rw [InfinityParameters318.coefficient_shape]
  simp only [linearCoefficient,map_mul,map_sub,map_one,substitution,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,LinearRootCoordinate318.baseSubstitution,
    Polynomial.aeval_C,Polynomial.aeval_X,Polynomial.C_0,add_zero]
  simp only [div_eq_mul_inv,Units.val_inv_eq_inv_val,map_mul,Polynomial.algebraMap_eq]
  ring

theorem substitution_denominator :
    substitution c (reciprocalDenominator c)=denominator c := by
  simp only [reciprocalDenominator,map_prod,substitution_coefficient,denominator]

theorem reciprocalDenominator_at_zero :
    Polynomial.eval 0 (reciprocalDenominator c)=∏j:Fin 3,(c j.succ:ℚ)/(c 0:ℚ) := by
  simp only [reciprocalDenominator,Polynomial.eval_prod,linearCoefficient,eval_mul,eval_sub,eval_C,eval_X,eval_one,mul_zero,sub_zero,mul_one]

theorem reciprocalDenominator_ne_zero : reciprocalDenominator c≠0 := by
  intro h
  exact denominator_ne_zero c (by rw [←substitution_denominator,h,map_zero])

/-- Finiteness of the genuine degree-two substitution is proved through
the actual monic quadratic root ring, not assumed. -/
theorem substitution_finite : (substitution c).Finite := by
  have he:(LinearRootCoordinate318.coordinateEquiv (c 0) (0:ℚ)).toRingHom.comp
      (algebraMap R (LinearRootCoordinate318.Root (c 0) (0:ℚ)))=substitution c := by
    apply RingHom.ext
    intro p
    exact LinearRootCoordinate318.coordinate_base (c 0) (0:ℚ) p
  rw [←he]
  apply RingHom.Finite.comp (RingEquiv.finite _)
  exact RingHom.finite_algebraMap.mpr (FourRootOrder318.root_finite _)

local instance targetLocalization :
    IsLocalization.Away (substitution c (reciprocalDenominator c)) (OpenBase c) := by
  rw [substitution_denominator]
  infer_instance

@[expose] def openMap : ReciprocalOpen c→+*OpenBase c :=
  IsLocalization.Away.map (ReciprocalOpen c) (OpenBase c) (substitution c)
    (reciprocalDenominator c)

theorem openMap_finite : (openMap c).Finite :=
  RingHom.localization_away_map_finite R R (ReciprocalOpen c) (OpenBase c)
    (substitution c) (reciprocalDenominator c) (substitution_finite c)

@[expose] def chartMap : ReciprocalOpen c→+*OpenOrder c :=
  (algebraMap (OpenBase c) (OpenOrder c)).comp (openMap c)

/-- The full infinity neighborhood is finite over the actual reciprocal
projective-line open, not only over the root-coordinate u-line. -/
theorem chartMap_finite : (chartMap c).Finite := by
  apply RingHom.Finite.comp _ (openMap_finite c)
  exact RingHom.finite_algebraMap.mpr (finite_free_etale_rank_eight c).1

end ReciprocalInfinityBase318
