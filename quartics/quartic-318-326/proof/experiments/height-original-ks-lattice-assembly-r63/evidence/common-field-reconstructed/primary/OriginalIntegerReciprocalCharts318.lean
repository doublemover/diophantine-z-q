module
public import OriginalIntegerAffineModel318
public import IntegralFourRootReciprocalCharts318
public section
noncomputable section
namespace OriginalIntegerReciprocalCharts318
open Polynomial
variable (c : Fin 4 → ℚˣ)

@[expose] def integralTwist (i : Fin 4) : ℤ :=
  (c i : ℚ).num * ((c i : ℚ).den : ℤ)

/-- These finite-chart equations are definitionally the already constructed
integer affine model, not a newly chosen square-equivalent source. -/
theorem finiteCoefficient_eq (i : Fin 4) :
    IntegralFourRootReciprocalCharts318.finiteCoefficient (integralTwist c)
      OriginalIntegerAffineModel318.contacts i = OriginalIntegerAffineModel318.coefficient c i := rfl

abbrev ReciprocalOrder := IntegralFourRootReciprocalCharts318.ReciprocalOrder
  (integralTwist c) OriginalIntegerAffineModel318.contacts

theorem reciprocal_finite_free : Module.Finite ℤ[X] (ReciprocalOrder c) ∧
    Module.Free ℤ[X] (ReciprocalOrder c) :=
  IntegralFourRootReciprocalCharts318.reciprocal_chart_free _ _

theorem reciprocal_rank : Module.finrank ℤ[X] (ReciprocalOrder c) = 16 :=
  FourRootOrder318.rank_sixteen _

/-- Exact reciprocal transition of the original integer model after any
base change with an invertible chart coordinate. No prime is inverted. -/
@[expose] def overlap {S : Type*} [CommRing S] (s : Sˣ) :
    FourRootOrder318.Order (fun i => Polynomial.aeval (s : S)
      (IntegralFourRootReciprocalCharts318.reciprocalCoefficient (integralTwist c)
        OriginalIntegerAffineModel318.contacts i)) ≃ₐ[S]
    FourRootOrder318.Order (fun i => Polynomial.aeval ((s⁻¹ : Sˣ) : S)
      (OriginalIntegerAffineModel318.coefficient c i)) :=
  IntegralFourRootReciprocalCharts318.overlapEquiv (integralTwist c)
    OriginalIntegerAffineModel318.contacts s

end OriginalIntegerReciprocalCharts318
