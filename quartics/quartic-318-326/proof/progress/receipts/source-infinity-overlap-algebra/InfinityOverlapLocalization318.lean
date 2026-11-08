module
public import IntegralClosureOpen318
public import ReciprocalOverlapBase318
public import InfinityGlobalChart318
public import LocalizationSourceTransport318
public section
noncomputable section
namespace InfinityOverlapLocalization318
open Polynomial
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
abbrev R:=ℚ[X]
abbrev A:=ReciprocalInfinityBase318.ReciprocalOpen c
abbrev S:=ContactKummerOrder318.OpenBase
abbrev Source:=ContactKummerOrder318.OpenOrder c
abbrev Infinity:=InfinityOpenChart318.OpenOrder c
local instance baseAlgebra : Algebra (A c) S:=(InfinityGlobalBase318.sourceBaseMap c).toAlgebra
local instance sourceAlgebra : Algebra (A c) (Source c):=(InfinityGlobalBase318.sourceHom c).toAlgebra
local instance baseSMul : SMul (A c) S:=(baseAlgebra c).toSMul
local instance baseModule : Module (A c) S:=Algebra.toModule
local instance sourceSMul : SMul (A c) (Source c):=(sourceAlgebra c).toSMul
local instance sourceModule : Module (A c) (Source c):=Algebra.toModule
local instance sourceBaseSMul : SMul S (Source c):=(inferInstance:Algebra S (Source c)).toSMul
local instance sourceBaseModule : Module S (Source c):=Algebra.toModule
local instance sourceTower : IsScalarTower (A c) S (Source c):=
  IsScalarTower.of_algebraMap_eq (R:=A c) (S:=S) (A:=Source c) (fun _=>rfl)
local instance sourceFinite : Module.Finite S (Source c):=(ContactKummerOrder318.open_finite_free_etale c).1
local instance baseLocalization : IsLocalization.Away (algebraMap R (A c) X) S:=
  ReciprocalOverlapBase318.sourceBase_isLocalization c
local instance infinityAlgebra : Algebra (A c) (Infinity c):=(ReciprocalInfinityBase318.chartMap c).toAlgebra

/-- The actual map from the whole infinity order to the original unbranched
source, induced by the already identified integral closure, with no new field. -/
@[expose] def toOpen : Infinity c→+*Source c:=
  ((integralClosure (A c) (Source c)).val.toRingHom).comp
    (InfinityGlobalChart318.sourceClosureEquiv c).symm.toRingHom
local instance infinitySourceAlgebra : Algebra (Infinity c) (Source c):=(toOpen c).toAlgebra
local instance infinitySourceSMul : SMul (Infinity c) (Source c):=(infinitySourceAlgebra c).toSMul
local instance infinitySourceModule : Module (Infinity c) (Source c):=Algebra.toModule

@[simp] theorem toOpen_on_base (a:A c):
    toOpen c (algebraMap (A c) (Infinity c) a)=algebraMap (A c) (Source c) a:=by
  change (↑((InfinityGlobalChart318.sourceClosureEquiv c).symm
    (algebraMap (A c) (Infinity c) a)):Source c)=_
  rw [AlgEquiv.commutes]
  rfl

local instance infinitySourceTower : IsScalarTower (A c) (Infinity c) (Source c):=
  IsScalarTower.of_algebraMap_eq (fun a=>(toOpen_on_base c a).symm)

/-- The original Raw embeddings commute on every element of the entire order. -/
theorem toOpen_embedding (x:Infinity c):
    SourceOpenFractionField318.openEmbedding c (toOpen c x)=
      InfinityOpenFractionField318.openEmbedding c x:=by
  have h:=InfinityGlobalChart318.sourceClosureEquiv_embedding c
    ((InfinityGlobalChart318.sourceClosureEquiv c).symm x)
  change SourceOpenFractionField318.openEmbedding c
    (↑((InfinityGlobalChart318.sourceClosureEquiv c).symm x))=_
  simpa only [AlgEquiv.apply_symm_apply] using h.symm

theorem reciprocal_isLocalization :
    IsLocalization.Away (algebraMap (A c) (Infinity c) (algebraMap R (A c) X)) (Source c):=by
  letI:Algebra.IsIntegral S (Source c):=Algebra.IsIntegral.of_finite S (Source c)
  letI:=IntegralClosureOpen318.away_integralClosure (R:=A c) (A:=S) (B:=Source c)
    (algebraMap R (A c) X)
  letI:IsLocalization.Away
      ((InfinityGlobalChart318.sourceClosureEquiv c).symm.toRingEquiv
        (algebraMap (A c) (Infinity c) (algebraMap R (A c) X))) (Source c):=by
    simpa only [AlgEquiv.coe_toRingEquiv,AlgEquiv.commutes] using
      (inferInstance:IsLocalization.Away
        (algebraMap (A c) (integralClosure (A c) (Source c)) (algebraMap R (A c) X)) (Source c))
  exact LocalizationSourceTransport318.away (S:=integralClosure (A c) (Source c))
    (InfinityGlobalChart318.sourceClosureEquiv c).symm.toRingEquiv
    (algebraMap (A c) (Infinity c) (algebraMap R (A c) X)) (fun _=>rfl)

@[expose] def coordinate : Infinity c:=
  algebraMap (InfinityOpenChart318.OpenBase c) (Infinity c)
    (algebraMap R (InfinityOpenChart318.OpenBase c) X)

theorem reciprocal_coordinate :
    algebraMap (A c) (Infinity c) (algebraMap R (A c) X)=
      algebraMap ℚ (Infinity c) (↑((c 0)⁻¹):ℚ)*(coordinate c)^2:=by
  change ReciprocalInfinityBase318.chartMap c (algebraMap R (A c) X)=_
  unfold ReciprocalInfinityBase318.chartMap ReciprocalInfinityBase318.openMap
  simp only [RingHom.comp_apply,IsLocalization.Away.map,IsLocalization.map_eq]
  rw [ReciprocalInfinityBase318.substitution_X]
  simp only [map_mul,map_pow,coordinate]
  congr 1

end InfinityOverlapLocalization318
