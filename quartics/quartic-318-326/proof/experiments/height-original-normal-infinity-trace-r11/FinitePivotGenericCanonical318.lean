module
public import FinitePivotIntegralCanonicalTensors318
public import FiniteDualDifferentialRealization318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace FinitePivotGenericCanonical318
open Polynomial FinitePivotCanonicalSource318 FinitePivotCanonicalCoefficients318
open FinitePivotIntegralCanonicalTensors318 NormalizedDualBicanonicalSections318
open scoped TensorProduct
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (rho : V) (u : Vˣ) (d a : Fin 4 → V) (i : Fin 4)
local notation "C" => FinitePivotCanonicalSource318.Chart V rho u d a i
/-- The literal different-unit open of the integral smooth chart. -/
@[expose] abbrev Generic := Localization.Away (different V rho u d a i)
local notation "B" => Generic V rho u d a i
/-- The actual structural base action is the explicit composite through
this very integral chart, rather than an inferred transitive algebra. -/
instance genericAlgebra : Algebra V B :=
  ((algebraMap C B).comp (algebraMap V C)).toAlgebra
instance genericTower : IsScalarTower V C B :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
@[expose] def baseMap : C →ₐ[V] B := IsScalarTower.toAlgHom V C B
@[expose] def differentUnit : Bˣ :=
  (IsLocalization.Away.algebraMap_isUnit (different V rho u d a i)).unit
lemma differentUnit_value : (differentUnit V rho u d a i:B)=algebraMap C B (different V rho u d a i) :=
  (IsLocalization.Away.algebraMap_isUnit (different V rho u d a i)).unit_spec

variable (hd : d i=(u:V)*rho)
@[expose] def genericSource : DVRNormalizedFiniteOrder318.Order V d a →+* B :=
  (algebraMap C B).comp (sourceMap V rho u d a i hd)
lemma genericSource_polynomial (p : V[X]) : genericSource V rho u d a i hd
    (algebraMap V[X] (DVRNormalizedFiniteOrder318.Order V d a) p)=
      algebraMap C B (scalarMap V rho u d a i p) := by
  change algebraMap C B (sourceMap V rho u d a i hd _) = _
  rw [sourceMap_polynomial]
lemma genericSource_root (k : Fin 4) : genericSource V rho u d a i hd
    (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient V d a) k)=
      algebraMap C B (originalRoot V rho u d a i k) := by
  change algebraMap C B (sourceMap V rho u d a i hd _) = _
  rw [sourceMap_root]

@[expose] def omega : KaehlerDifferential V B :=
  (↑(differentUnit V rho u d a i)⁻¹:B) • KaehlerDifferential.D V B
    (algebraMap C B (t V rho u d a i))
/-- Actual map out of the ENTIRE original finite-dual tensor square. -/
@[expose] def realization : FiniteDualTransport318.Square (R:=V[X])
    (A:=DVRNormalizedFiniteOrder318.Order V d a) →ₛₗ[genericSource V rho u d a i hd]
      KaehlerDifferential V B ⊗[B] KaehlerDifferential V B :=
  FiniteDualDifferentialRealization318.squareRealization
    (FourRootIntegralDuality318.frame (DVRNormalizedFiniteOrder318.coefficient V d a))
    (genericSource V rho u d a i hd) (omega V rho u d a i)
lemma realization_section (p : V[X]) : realization V rho u d a i hd (finiteSection V d a p)=
    algebraMap C B (scalarMap V rho u d a i p) • (omega V rho u d a i ⊗ₜ[B] omega V rho u d a i) := by
  rw [realization,finiteSection,FiniteDualDifferentialRealization318.squareRealization_frame,
    genericSource_polynomial]

variable (h2 : IsUnit (2:V))
include h2 in
theorem section0_integral : realization V rho u d a i hd (section0Finite V d a)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V) (baseMap V rho u d a i)
      (integral0 V rho u d a i) := by
  rw [section0Finite,realization_section]
  change (baseMap V rho u d a i) (scalarMap V rho u d a i (finite0 V d)) • _ = _
  have hp : scalarMap V rho u d a i (finite0 V d)=
      algebraMap V C (sectionCoefficient V d) := by
    simp only [scalarMap,OddTwistDilatationSourceMap318.originalScalar,finite0,coe_eval₂RingHom,eval₂_C]
  rw [hp]
  exact FinitePivotIntegralCanonicalTensors318.realization V rho u d a i (baseMap V rho u d a i) h2
    (differentUnit V rho u d a i) (differentUnit_value V rho u d a i) _ _
    (coefficient0_identity V rho u d a i hd)
include h2 in
theorem section1_integral : realization V rho u d a i hd (section1Finite V d a)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V) (baseMap V rho u d a i)
      (integral1 V rho u d a i) := by
  rw [section1Finite,realization_section]
  change (baseMap V rho u d a i) (scalarMap V rho u d a i (finite1 V d)) • _ = _
  have hp : scalarMap V rho u d a i (finite1 V d)=
      t V rho u d a i*algebraMap V C (sectionCoefficient V d) := by
    simp only [scalarMap,OddTwistDilatationSourceMap318.originalScalar,finite1,coe_eval₂RingHom,eval₂_mul,eval₂_C,eval₂_X]; rfl
  rw [hp]
  exact FinitePivotIntegralCanonicalTensors318.realization V rho u d a i (baseMap V rho u d a i) h2
    (differentUnit V rho u d a i) (differentUnit_value V rho u d a i) _ _
    (coefficient1_identity V rho u d a i hd)
end FinitePivotGenericCanonical318
