module
public import ActualLocalizationDifferentialFrame318
public import ActualCanonicalFrameOrderInvariant318
public import Mathlib.RingTheory.Etale.Basic
public section
noncomputable section
namespace ActualPrincipalStalkDifferentialFrame318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (R:Type*) [CommRing R] [IsDomain R] [Algebra ℂ R]
variable (p:Ideal R) [p.IsPrime] (d:R) (hd:d∉p)
abbrev Chart:=Localization.Away d
abbrev Stalk:=Localization.AtPrime p
abbrev Field:=FractionRing R
lemma denominator_ne:d≠0:=fun h=>hd (h.symm ▸ p.zero_mem)
/-- The principal chart maps to the genuine original local ring at p;
its inverted denominator is a unit because p lies in this chart. -/
@[expose] def chartToStalk:Chart R d→+*Stalk R p:=
  IsLocalization.Away.lift d (IsLocalization.map_units (Stalk R p) ⟨d,hd⟩)
local instance chartStalkAlgebra:Algebra (Chart R d) (Stalk R p):=
  (chartToStalk R p d hd).toAlgebra
local instance chartStalkTower:IsScalarTower R (Chart R d) (Stalk R p):=
  IsScalarTower.of_algebraMap_eq (fun x=>(IsLocalization.Away.lift_eq _ _ x).symm)
local instance complexStalkTower:IsScalarTower ℂ (Chart R d) (Stalk R p):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply ℂ R (Chart R d)]
  rw [←IsScalarTower.algebraMap_apply R (Chart R d) (Stalk R p)]
  exact IsScalarTower.algebraMap_apply ℂ R (Stalk R p) c
local instance sourceChartEtale:Algebra.FormallyEtale R (Chart R d):=
  Algebra.FormallyEtale.of_isLocalization (Submonoid.powers d)
local instance sourceStalkEtale:Algebra.FormallyEtale R (Stalk R p):=
  Algebra.FormallyEtale.of_isLocalization p.primeCompl
local instance chartStalkEtale:Algebra.FormallyEtale (Chart R d) (Stalk R p):=
  Algebra.FormallyEtale.of_restrictScalars (R:=R)
@[expose] def stalkFrame(e:KaehlerDifferential ℂ (Chart R d)≃ₗ[Chart R d]Chart R d):
    KaehlerDifferential ℂ (Stalk R p)≃ₗ[Stalk R p]Stalk R p:=
  EtaleDifferentialFrame318.ofFormallyEtale e
lemma chartToStalk_on_source(x:R):
    chartToStalk R p d hd (algebraMap R (Chart R d) x)=algebraMap R (Stalk R p) x:=
  IsLocalization.Away.lift_eq _ _ _
lemma stalkFrame_D(e:KaehlerDifferential ℂ (Chart R d)≃ₗ[Chart R d]Chart R d)(x:Chart R d):
    stalkFrame R p d hd e (KaehlerDifferential.D ℂ (Stalk R p) (chartToStalk R p d hd x))=
      chartToStalk R p d hd (e (KaehlerDifferential.D ℂ (Chart R d) x)):=
  ActualEtaleFrameNormalization318.ofFormallyEtale_D e x

local instance stalkFieldAlgebra:Algebra (Stalk R p) (Field R):=
  (ActualPrimeMeromorphicOrder318.embedding R p).toAlgebra
local instance sourceFieldTower:IsScalarTower R (Stalk R p) (Field R):=
  IsScalarTower.of_algebraMap_eq (fun x=>(IsLocalization.lift_eq _ x).symm)
local instance complexFieldTower:IsScalarTower ℂ (Stalk R p) (Field R):=by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply ℂ R (Stalk R p)]
  rw [←IsScalarTower.algebraMap_apply R (Stalk R p) (Field R)]
  exact IsScalarTower.algebraMap_apply ℂ R (Field R) c
local instance stalkFraction:IsFractionRing (Stalk R p) (Field R):=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl (Stalk R p) (Field R)
local instance stalkFieldEtale:Algebra.FormallyEtale (Stalk R p) (Field R):=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Stalk R p))
@[expose] def throughStalk(e:KaehlerDifferential ℂ (Chart R d)≃ₗ[Chart R d]Chart R d):
    KaehlerDifferential ℂ (Field R)≃ₗ[Field R]Field R:=
  EtaleDifferentialFrame318.ofFormallyEtale (stalkFrame R p d hd e)
lemma throughStalk_D(e:KaehlerDifferential ℂ (Chart R d)≃ₗ[Chart R d]Chart R d)(x:R):
    throughStalk R p d hd e (KaehlerDifferential.D ℂ (Field R) (algebraMap R (Field R) x))=
      ActualPrimeMeromorphicOrder318.embedding R p
        (chartToStalk R p d hd (e (KaehlerDifferential.D ℂ (Chart R d)
          (algebraMap R (Chart R d) x)))):=by
  rw [←ActualPrimeMeromorphicOrder318.on_source R p x]
  rw [throughStalk,ActualEtaleFrameNormalization318.ofFormallyEtale_D]
  rw [←chartToStalk_on_source R p d hd x,stalkFrame_D]

/-- Two genuine rank-one frames normalized by the SAME differential
are equal, not merely related by an unspecified fraction-field scalar. -/
lemma frame_eq_of_normalized {K M:Type*} [Field K] [AddCommGroup M] [Module K M]
    (e f:M≃ₗ[K]K)(ω:M)(he:e ω=1)(hf:f ω=1):e=f:=by
  apply LinearEquiv.ext
  intro η
  have hη:η=e η • ω:=by
    apply e.injective
    rw [map_smul,he,smul_eq_mul,mul_one]
  calc
    e η=f (e η • ω):=by rw [map_smul,hf,smul_eq_mul,mul_one]
    _=f η:=congrArg f hη.symm

/-- Extending a proved principal-chart frame through the ACTUAL stalk
agrees exactly with its previous direct extension to the SAME original
fraction field. The common original root differential fixes the scalar. -/
theorem throughStalk_eq_direct
    (e:KaehlerDifferential ℂ (Chart R d)≃ₗ[Chart R d]Chart R d)(x:R)
    (hx:e (KaehlerDifferential.D ℂ (Chart R d) (algebraMap R (Chart R d) x))=1):
    throughStalk R p d hd e=
      ActualLocalizationDifferentialFrame318.frame R d (denominator_ne R p d hd) e:=by
  apply frame_eq_of_normalized _ _
    (KaehlerDifferential.D ℂ (Field R) (algebraMap R (Field R) x))
  · rw [throughStalk_D,hx,map_one,map_one]
  · rw [←ActualLocalizationDifferentialFrame318.on_source R d (denominator_ne R p d hd) x]
    rw [ActualLocalizationDifferentialFrame318.frame_D,hx,map_one]
end ActualPrincipalStalkDifferentialFrame318
