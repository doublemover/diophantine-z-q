module
public import ActualPrincipalStalkDifferentialFrame318
public import FourRootActualBaseDifferentialOrders318
public section
noncomputable section
namespace FourRootActualFiniteStalkFrame318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
open FourRootActualFractionField318 FourRootActualFiniteBranchChart318
open FourRootActualFiniteDifferentialOrders318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ)(hb:Function.Injective b)(p:FinitePoints b)
local instance affineDedekind:IsDedekindDomain (A b):=FourRootActualDedekind318.finite_dedekind b hb
local instance pointPrime:(finitePrime b p).IsPrime:=finite_prime b p
abbrev LocalRing:=Localization.AtPrime (finitePrime b p)
/-- A frame of the ACTUAL algebraic Kähler module of the original
point's local ring, constructed from its proved chart neighborhood. -/
@[expose] def localFrame:KaehlerDifferential ℂ (LocalRing b p)≃ₗ[LocalRing b p]LocalRing b p:=
  ActualPrincipalStalkDifferentialFrame318.stalkFrame (A b) (finitePrime b p)
    (denominator b (chartIndex b p)) (chartIndex_neighborhood b hb p)
    (FourRootActualBranchKaehler318.sourceFrame b (chartIndex b p))
@[expose] def fieldFrame:KaehlerDifferential ℂ (FractionRing (A b))≃ₗ[FractionRing (A b)]FractionRing (A b):=
  ActualPrincipalStalkDifferentialFrame318.throughStalk (A b) (finitePrime b p)
    (denominator b (chartIndex b p)) (chartIndex_neighborhood b hb p)
    (FourRootActualBranchKaehler318.sourceFrame b (chartIndex b p))
lemma fieldFrame_eq:fieldFrame b hb p=FourRootActualMeromorphicFinite318.frame b hb (chartIndex b p):=by
  apply ActualPrincipalStalkDifferentialFrame318.throughStalk_eq_direct
    (A b) (finitePrime b p) (denominator b (chartIndex b p)) (chartIndex_neighborhood b hb p)
    (FourRootActualBranchKaehler318.sourceFrame b (chartIndex b p))
    (FourRootAffineCoordinateRing318.coordinate b (some (chartIndex b p)))
  rw [←FourRootActualBranchKaehler318.source_coordinate_original]
  exact FourRootActualBranchKaehler318.source_normalized b (chartIndex b p)
/-- The previously valued meromorphic coefficient is now the exact
coefficient of dt in the extension of a genuine original STALK frame. -/
lemma original_dt_coefficient:
    fieldFrame b hb p (KaehlerDifferential.D ℂ (FractionRing (A b))
      (FourRootActualMeromorphicFinite318.t b))=coefficient b hb p:=by
  rw [fieldFrame_eq]
  rfl
local instance localDvr:IsDiscreteValuationRing (LocalRing b p):=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (A b)
    (FourRootLocalDifferentMultiplicity318.all_finite_prime_nonzero b hb p) (LocalRing b p)
lemma branch_order(i:Fin 4)(hp:p.val.1=b i):
    ActualPrimeMeromorphicOrder318.order (A b) (finitePrime b p)
      (fieldFrame b hb p (KaehlerDifferential.D ℂ (FractionRing (A b))
        (FourRootActualMeromorphicFinite318.t b)))=1:=by
  rw [original_dt_coefficient]
  exact FourRootActualFiniteDifferentialOrders318.branch_order b hb p i hp
lemma regular_order(hp:∀i,p.val.1≠b i):
    ActualPrimeMeromorphicOrder318.order (A b) (finitePrime b p)
      (fieldFrame b hb p (KaehlerDifferential.D ℂ (FractionRing (A b))
        (FourRootActualMeromorphicFinite318.t b)))=0:=by
  rw [original_dt_coefficient]
  exact FourRootActualFiniteDifferentialOrders318.regular_order b hb p hp
end FourRootActualFiniteStalkFrame318

namespace FourRootActualInfinityStalkFrame318
open FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (b:Fin 4→ℂ)(hb:Function.Injective b)(p:InfinityPoints b)(hp:p.val.1=0)
abbrev I:=FourRootInfinityCoordinateRing318.Ring b
local instance infinityDedekind:IsDedekindDomain (I b):=FourRootActualDedekind318.infinity_dedekind b hb
local instance pointPrime:(infinityPrime b p).IsPrime:=infinity_prime b p
abbrev LocalRing:=Localization.AtPrime (infinityPrime b p)
lemma neighborhood:FourRootActualMeromorphicInfinity318.d b hb∉infinityPrime b p:=
  FourRootActualKaehlerNeighborhoods318.infinity_neighborhood b hb p hp
@[expose] def localFrame:KaehlerDifferential ℂ (LocalRing b p)≃ₗ[LocalRing b p]LocalRing b p:=
  ActualPrincipalStalkDifferentialFrame318.stalkFrame (I b) (infinityPrime b p)
    (FourRootActualMeromorphicInfinity318.d b hb) (neighborhood b hb p hp)
    (FourRootActualInfinityKaehler318.frame b hb)
@[expose] def fieldFrame:KaehlerDifferential ℂ (FractionRing (I b))≃ₗ[FractionRing (I b)]FractionRing (I b):=
  ActualPrincipalStalkDifferentialFrame318.throughStalk (I b) (infinityPrime b p)
    (FourRootActualMeromorphicInfinity318.d b hb) (neighborhood b hb p hp)
    (FourRootActualInfinityKaehler318.frame b hb)
lemma fieldFrame_eq:fieldFrame b hb p hp=FourRootActualMeromorphicInfinity318.frame b hb:=by
  apply ActualPrincipalStalkDifferentialFrame318.throughStalk_eq_direct
    (I b) (infinityPrime b p) (FourRootActualMeromorphicInfinity318.d b hb)
    (neighborhood b hb p hp) (FourRootActualInfinityKaehler318.frame b hb)
    (FourRootInfinityCoordinateRing318.coordinate b none)
  exact FourRootActualInfinityKaehler318.coordinate_normalized b hb
local instance localDvr:IsDiscreteValuationRing (LocalRing b p):=
  FourRootInfinityDifferentMultiplicity318.local_dvr b hb p hp
/-- All eight original infinity centers retain the true original dt
pole order -3. The genuine stalk coordinate is u, not the base v=u². -/
lemma original_dt_order:
    ActualPrimeMeromorphicOrder318.order (I b) (infinityPrime b p)
      (fieldFrame b hb p hp (KaehlerDifferential.D ℂ (FractionRing (I b))
        (FourRootActualMeromorphicInfinity318.t b hb)))=-3:=by
  rw [fieldFrame_eq]
  exact FourRootActualInfinityDifferentialOrders318.order_minus_three b hb p hp
end FourRootActualInfinityStalkFrame318
