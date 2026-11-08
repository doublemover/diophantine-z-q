module
public import InfinityGlobalBase318
public import NormalChart318
public section
noncomputable section
namespace InfinityGlobalChart318
open Polynomial CategoryTheory AlgebraicGeometry
open InfinityGlobalBase318
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev InfinityOrder:=InfinityOpenChart318.OpenOrder c
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceDomain : IsDomain (Source c):=ContactKummerOpenDomain318.open_domain c
local instance sourceNormal : IsIntegrallyClosed (Source c):=SourceNormalChart318.source_integrallyClosed c
local instance sourceAlgebra : Algebra (A c) (Source c):=(sourceHom c).toAlgebra
local instance sourceSMul : SMul (A c) (Source c):=(sourceAlgebra c).toSMul
local instance sourceModule : Module (A c) (Source c):=Algebra.toModule
local instance sourceOriginalAlgebra : Algebra (Source c) (L c):=
  (SourceOpenFractionField318.openEmbedding c).toAlgebra
local instance sourceFraction : IsFractionRing (Source c) (L c):=
  SourceOpenFractionField318.open_fractionField c
local instance baseAlgebra : Algebra (A c) (L c):=
  (ReciprocalInfinityNormalization318.reciprocalEmbedding c).toAlgebra
local instance baseSMul : SMul (A c) (L c):=(baseAlgebra c).toSMul
local instance baseModule : Module (A c) (L c):=Algebra.toModule
local instance sourceTower : IsScalarTower (A c) (Source c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=A c) (S:=Source c) (A:=L c)
    (fun x=>(RingHom.congr_fun (embedding_square c) x).symm)

/-- The actual source-chart integral closure is also the closure in the
original full function field, because the entire source is normal with that
specified fraction field. -/
theorem sourceClosure_isIntegralClosure :
    IsIntegralClosure (integralClosure (A c) (Source c)) (A c) (L c) :=
  IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
    (A c) (integralClosure (A c) (Source c)) (Source c) (L c)

local instance infinityAlgebra : Algebra (A c) (InfinityOrder c):=
  (ReciprocalInfinityBase318.chartMap c).toAlgebra
local instance infinitySMul : SMul (A c) (InfinityOrder c):=(infinityAlgebra c).toSMul
local instance infinityModule : Module (A c) (InfinityOrder c):=Algebra.toModule
local instance infinityOriginalAlgebra : Algebra (InfinityOrder c) (L c):=
  (InfinityOpenFractionField318.openEmbedding c).toAlgebra
local instance infinityTower : IsScalarTower (A c) (InfinityOrder c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=A c) (S:=InfinityOrder c) (A:=L c) (fun _=>rfl)

/-- The source normalization over this open and the explicit infinity
order are compared in the same field, with their exact base maps. -/
@[expose] def sourceClosureEquiv : integralClosure (A c) (Source c)≃ₐ[A c]InfinityOrder c := by
  let :=sourceClosure_isIntegralClosure c
  let :=ReciprocalInfinityNormalization318.actual_integralClosure c
  exact IsIntegralClosure.equiv (A c) (integralClosure (A c) (Source c)) (L c) (InfinityOrder c)

theorem sourceClosureEquiv_embedding (x:integralClosure (A c) (Source c)) :
    InfinityOpenFractionField318.openEmbedding c (sourceClosureEquiv c x)=
      SourceOpenFractionField318.openEmbedding c x.val := by
  let :=sourceClosure_isIntegralClosure c
  let :=ReciprocalInfinityNormalization318.actual_integralClosure c
  exact IsIntegralClosure.algebraMap_equiv (A c) (integralClosure (A c) (Source c))
    (L c) (InfinityOrder c) x

@[expose] def sectionsEquiv_of_factor {A' B':CommRingCat} {Y:Scheme}
    (φ:A'⟶B') (j:Spec A'⟶Y) [IsOpenImmersion j]
    (f:Spec B'⟶Y) [QuasiCompact f] [QuasiSeparated f] (hf:f=Spec.map φ≫j) :
    letI:=φ.hom.toAlgebra
    Γ(f.normalization,f.fromNormalization⁻¹ᵁ(j ''ᵁ ⊤))≃+*integralClosure A' B' := by
  subst f
  exact NormalChart318.sectionsEquiv φ j

@[expose] def chartRing : CommRingCat :=
  Γ((ContactProjectiveModel318.coverMap c).normalization,
    (ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ(baseOpen c ''ᵁ ⊤))

/-- The ring of the actual infinity open of the actual globally glued
normalization is the explicit whole infinity order. -/
@[expose] def actualChartEquiv : chartRing c≃+*InfinityOrder c := by
  let e:=sectionsEquiv_of_factor (CommRingCat.ofHom (sourceHom c)) (baseOpen c)
    (ContactProjectiveModel318.coverMap c) (factorization c)
  exact e.trans (sourceClosureEquiv c).toRingEquiv
end InfinityGlobalChart318
