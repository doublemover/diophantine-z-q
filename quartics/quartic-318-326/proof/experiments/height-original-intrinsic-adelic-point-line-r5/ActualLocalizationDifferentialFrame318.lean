module
public import ActualEtaleFrameNormalization318
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public section
noncomputable section
namespace ActualLocalizationDifferentialFrame318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (R:Type*) [CommRing R] [IsDomain R] [Algebra ℂ R]
variable (d:R)(hd:d≠0)
abbrev Chart:=Localization.Away d
abbrev Field:=FractionRing R
local instance chartDomain:IsDomain (Chart R d):=Localization.Away.isDomain hd
@[expose] def embedding:Chart R d→+*Field R:=
  IsLocalization.Away.lift (g:=algebraMap R (Field R)) d
    (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R (Field R))).mpr hd))
local instance chartAlgebra:Algebra (Chart R d) (Field R):=(embedding R d hd).toAlgebra
local instance sourceTower:IsScalarTower R (Chart R d) (Field R):=
  IsScalarTower.of_algebraMap_eq (fun x=>(IsLocalization.Away.lift_eq _ _ x).symm)
local instance complexTower:IsScalarTower ℂ (Chart R d) (Field R):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply ℂ R (Chart R d)]
  rw [←IsScalarTower.algebraMap_apply R (Chart R d) (Field R)]
  exact IsScalarTower.algebraMap_apply ℂ R (Field R) c
lemma actual_fractionField:IsFractionRing (Chart R d) (Field R):=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers d) (Chart R d) (Field R)
local instance chartFraction:IsFractionRing (Chart R d) (Field R):=actual_fractionField R d hd
local instance fractionEtale:Algebra.FormallyEtale (Chart R d) (Field R):=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Chart R d))
/-- Extend the actual intrinsic chart frame to the SAME original
fraction field, not to a new unrelated meromorphic coordinate field. -/
@[expose] def frame(e:KaehlerDifferential ℂ (Chart R d)≃ₗ[Chart R d]Chart R d):
    KaehlerDifferential ℂ (Field R)≃ₗ[Field R]Field R:=
  EtaleDifferentialFrame318.ofFormallyEtale e
lemma on_source(x:R):embedding R d hd (algebraMap R (Chart R d) x)=algebraMap R (Field R) x:=
  IsLocalization.Away.lift_eq _ _ x
lemma frame_D(e:KaehlerDifferential ℂ (Chart R d)≃ₗ[Chart R d]Chart R d)(x:Chart R d):
    frame R d hd e (KaehlerDifferential.D ℂ (Field R) (embedding R d hd x))=
      embedding R d hd (e (KaehlerDifferential.D ℂ (Chart R d) x)):=
  ActualEtaleFrameNormalization318.ofFormallyEtale_D e x
end ActualLocalizationDifferentialFrame318
