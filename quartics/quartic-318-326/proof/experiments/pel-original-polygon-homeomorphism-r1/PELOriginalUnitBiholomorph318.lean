module
public import PELComplexPeriodSurface318
public import QuaternionicUnitPeriodTransport318
public import DiscreteComplexPeriodEquiv318
public section
noncomputable section
namespace PELOriginalUnitBiholomorph318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318 QuaternionicUnitPeriodTransport318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELComplexPeriodSurface318 DiscreteComplexPeriodEquiv318
open scoped Manifold ContDiff
set_option maxHeartbeats 1000000
variable (u : orderˣ) (hu : (unitMatrix representation order u).det=1)
variable (τ : ℂ) (hτ : 0<τ.im)

/-- The actual arithmetic translate of the original upper-half-plane parameter. -/
@[expose] def parameter : ℂ := unitParameter representation order u τ

include hu hτ in
theorem parameter_positive : 0<(parameter u τ).im :=
  mobius_positive _ hu τ hτ

include hu hτ in
theorem denominator_nonzero : unitDenominator representation order u τ≠0 :=
  denominator_ne _ hu τ hτ

/-- An equivalence of the SAME original order surfaces at arithmetic-related
parameters, not an equivalence of auxiliary lattices or merely of real tori. -/
@[expose] def transport : Surface τ ≃+ Surface (parameter u τ) :=
  quotientEquiv representation order u τ (denominator_nonzero u hu τ hτ)

local instance : DiscreteTopology (Periods τ) :=
  PELOriginalPeriodLattice318.original_discrete τ hτ
local instance : DiscreteTopology (Periods (parameter u τ)) :=
  PELOriginalPeriodLattice318.original_discrete _ (parameter_positive u hu τ hτ)

theorem transport_holomorphic :
    letI := surfaceCharts τ hτ
    letI := surfaceCharts (parameter u τ) (parameter_positive u hu τ hτ)
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (transport u hu τ hτ) :=
  congr_holomorphic (Periods τ) (Periods (parameter u τ)) _
    (exact_lattice_transport representation order u τ (denominator_nonzero u hu τ hτ))

theorem transport_inverse_holomorphic :
    letI := surfaceCharts τ hτ
    letI := surfaceCharts (parameter u τ) (parameter_positive u hu τ hτ)
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (transport u hu τ hτ).symm :=
  congr_symm_holomorphic (Periods τ) (Periods (parameter u τ)) _
    (exact_lattice_transport representation order u τ (denominator_nonzero u hu τ hτ))

theorem original_action_commutes (a : order) (p : Surface τ) :
    transport u hu τ hτ (QuaternionicOrderPeriodQuotient318.orderEnd representation order τ a p)=
      QuaternionicOrderPeriodQuotient318.orderEnd representation order (parameter u τ) a
        (transport u hu τ hτ p) :=
  quotientEquiv_order representation order u τ (denominator_nonzero u hu τ hτ) a p

/-- The SAME positive principal form is preserved. The denominator scalar
and right-unit inverse are used in the comparison, with no μ-sign change. -/
theorem riemann_transport (z w : ComplexVectors) :
    PELPeriodRiemannForm318.riemann (parameter u τ) (parameter_positive u hu τ hτ)
      (scalarEquiv (unitDenominator representation order u τ)
        (denominator_nonzero u hu τ hτ) z)
      (scalarEquiv (unitDenominator representation order u τ)
        (denominator_nonzero u hu τ hτ) w)=
    PELPeriodRiemannForm318.riemann τ hτ z w := by
  let g := unitMatrix representation order u
  let gi := unitMatrix representation order u⁻¹
  let M := (periodEquiv τ hτ).symm z
  let N := (periodEquiv τ hτ).symm w
  have hi : gi*g=1 := unitMatrix_inv_mul representation order u
  have hM : period (parameter u τ) (M*gi)=
      scalarEquiv (unitDenominator representation order u τ)
        (denominator_nonzero u hu τ hτ) z := by
    rw [show parameter u τ=mobius g τ from rfl,
      period_mobius g (M*gi) τ (denominator_nonzero u hu τ hτ),Matrix.mul_assoc,hi,
      Matrix.mul_one]
    exact congrArg (fun q => (unitDenominator representation order u τ)⁻¹ • q)
      ((periodEquiv τ hτ).apply_symm_apply z)
  have hN : period (parameter u τ) (N*gi)=
      scalarEquiv (unitDenominator representation order u τ)
        (denominator_nonzero u hu τ hτ) w := by
    rw [show parameter u τ=mobius g τ from rfl,
      period_mobius g (N*gi) τ (denominator_nonzero u hu τ hτ),Matrix.mul_assoc,hi,
      Matrix.mul_one]
    exact congrArg (fun q => (unitDenominator representation order u τ)⁻¹ • q)
      ((periodEquiv τ hτ).apply_symm_apply w)
  rw [←hM,←hN]
  change QuaternionicPeriodAlternating318.oriented
    ((periodEquiv (parameter u τ) _).symm (periodEquiv (parameter u τ) _ (M*gi)))
    ((periodEquiv (parameter u τ) _).symm (periodEquiv (parameter u τ) _ (N*gi)))=
      QuaternionicPeriodAlternating318.oriented M N
  rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
  have h := oriented_right g (M*gi) (N*gi) hu
  simpa only [Matrix.mul_assoc,hi,Matrix.mul_one] using h.symm
end PELOriginalUnitBiholomorph318
