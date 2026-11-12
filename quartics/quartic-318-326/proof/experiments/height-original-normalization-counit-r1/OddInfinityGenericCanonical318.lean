module
public import OddInfinityIntegralCanonicalTensors318
public import FiniteDualDifferentialRealization318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace OddInfinityGenericCanonical318
open Polynomial OddInfinityWholeModelMap318 OddInfinityCanonicalCoefficients318
open OddInfinityIntegralCanonicalTensors318 NormalizedDualBicanonicalSections318
open scoped TensorProduct
variable (V : Type*) [CommRing V] (pi : V) (u : Fin 4 → Vˣ) (d a : Fin 4 → V)
local notation "C" => OddInfinitySmoothChart318.ModelRing V pi u a
/-- The literal different-unit open of the integral smooth chart. -/
@[expose] abbrev Generic := Localization.Away (different V pi u a)
local notation "B" => Generic V pi u a
/-- The actual structural base action is the explicit composite through
this very integral chart, rather than an inferred transitive algebra. -/
instance genericAlgebra : Algebra V B :=
  ((algebraMap C B).comp (algebraMap V C)).toAlgebra
instance genericTower : IsScalarTower V C B :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
@[expose] def baseMap : C →ₐ[V] B := IsScalarTower.toAlgHom V C B
@[expose] def differentUnit : Bˣ :=
  (IsLocalization.Away.algebraMap_isUnit (different V pi u a)).unit
lemma differentUnit_value : (differentUnit V pi u a:B)=algebraMap C B (different V pi u a) :=
  (IsLocalization.Away.algebraMap_isUnit (different V pi u a)).unit_spec

variable (ha : a 0=0) (hd : ∀ i,d i=(u i:V)*pi)
@[expose] def genericSource : DVRNormalizedInfinityOrder318.Order V d a →+* B :=
  (algebraMap C B).comp (sourceMap V pi u d a ha hd)
lemma genericSource_polynomial (p : V[X]) : genericSource V pi u d a ha hd
    (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V d a) p)=
      algebraMap C B (scalarMap V pi u a p) := by
  change algebraMap C B (sourceMap V pi u d a ha hd _) = _
  rw [sourceMap_polynomial]
lemma genericSource_root (i : Fin 4) : genericSource V pi u d a ha hd
    (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient V d a) i)=
      algebraMap C B (signedRoot V pi u a i) := by
  change algebraMap C B (sourceMap V pi u d a ha hd _) = _
  rw [sourceMap_root]

@[expose] def omega : KaehlerDifferential V B :=
  (↑(differentUnit V pi u a)⁻¹:B) • KaehlerDifferential.D V B
    (algebraMap C B (s V pi u a))
/-- Actual map out of the ENTIRE original finite-dual tensor square. -/
@[expose] def realization : FiniteDualTransport318.Square (R:=V[X])
    (A:=DVRNormalizedInfinityOrder318.Order V d a) →ₛₗ[genericSource V pi u d a ha hd]
      KaehlerDifferential V B ⊗[B] KaehlerDifferential V B :=
  FiniteDualDifferentialRealization318.squareRealization
    (FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient V d a))
    (genericSource V pi u d a ha hd) (omega V pi u a)
lemma realization_section (p : V[X]) : realization V pi u d a ha hd (infinitySection V d a p)=
    algebraMap C B (scalarMap V pi u a p) • (omega V pi u a ⊗ₜ[B] omega V pi u a) := by
  rw [realization,infinitySection,FiniteDualDifferentialRealization318.squareRealization_frame,
    genericSource_polynomial]

variable (h2 : IsUnit (2:V))
include h2 in
theorem section0_integral : realization V pi u d a ha hd (section0Infinity V d a)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V) (baseMap V pi u a)
      (integral0 V pi u a) := by
  rw [section0Infinity,realization_section]
  change (baseMap V pi u a) (scalarMap V pi u a (infinity0 V d)) • _ = _
  have hp : scalarMap V pi u a (infinity0 V d)=
      algebraMap V C (sectionCoefficient V d)*(s V pi u a)^4 := by
    simp only [scalarMap,infinity0,coe_eval₂RingHom,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
  rw [hp]
  exact OddInfinityIntegralCanonicalTensors318.realization V pi u a (baseMap V pi u a) h2
    (differentUnit V pi u a) (differentUnit_value V pi u a) _ _
    (coefficient0_identity V pi u d a hd)
include h2 in
theorem section1_integral : realization V pi u d a ha hd (section1Infinity V d a)=
    BaseChangingDifferentialTensor318.tensorMap (S:=V) (baseMap V pi u a)
      (integral1 V pi u a) := by
  rw [section1Infinity,realization_section]
  change (baseMap V pi u a) (scalarMap V pi u a (infinity1 V d)) • _ = _
  have hp : scalarMap V pi u a (infinity1 V d)=
      algebraMap V C (sectionCoefficient V d)*(s V pi u a)^3 := by
    simp only [scalarMap,infinity1,coe_eval₂RingHom,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
  rw [hp]
  exact OddInfinityIntegralCanonicalTensors318.realization V pi u a (baseMap V pi u a) h2
    (differentUnit V pi u a) (differentUnit_value V pi u a) _ _
    (coefficient1_identity V pi u d a hd)
end OddInfinityGenericCanonical318
