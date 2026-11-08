module
public import SourceNormalChart318
public import ContactGlobalProper318
public import InfinityGlobalChart318
public section
noncomputable section
namespace SourceClosureComparison318
open CategoryTheory AlgebraicGeometry
open ContactKummerOrder318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c:Fin 4→ℚˣ)
abbrev L:=SourceFractionField318.L c
local instance originalField : Field (L c):=(KummerTensorField318.source_raw_field c).toField
local instance sourceDomain : IsDomain (SourceOrder c):=source_domain c
local instance sourceFinite : Module.Finite R (SourceOrder c):=(source_finite_free c).1
local instance openDomain : IsDomain (OpenOrder c):=ContactKummerOpenDomain318.open_domain c
local instance openNormal : IsIntegrallyClosed (OpenOrder c):=SourceNormalChart318.source_integrallyClosed c
local instance openAlgebra : Algebra R (OpenOrder c):=(ContactGlobalProper318.finitePolynomial c).toAlgebra
local instance openSMul : SMul R (OpenOrder c):=(openAlgebra c).toSMul
local instance openModule : Module R (OpenOrder c):=Algebra.toModule
local instance sourceOriginalAlgebra : Algebra (SourceOrder c) (L c):=(embedding c).toAlgebra
local instance sourceFraction : IsFractionRing (SourceOrder c) (L c):=SourceFractionField318.actual_fractionField c
local instance openOriginalAlgebra : Algebra (OpenOrder c) (L c):=(SourceOpenFractionField318.openEmbedding c).toAlgebra
local instance openFraction : IsFractionRing (OpenOrder c) (L c):=SourceOpenFractionField318.open_fractionField c
local instance baseOriginalAlgebra : Algebra R (L c):=
  ((algebraMap K (L c)).comp (algebraMap R K)).toAlgebra
local instance baseSMul : SMul R (L c):=(baseOriginalAlgebra c).toSMul
local instance baseModule : Module R (L c):=Algebra.toModule
local instance selfTower : IsScalarTower R R (L c):=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=R) (A:=L c) (fun _=>rfl)
local instance sourceTower : IsScalarTower R (SourceOrder c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=SourceOrder c) (A:=L c)
    (fun p=>(SourceFractionField318.embedding_on_polynomial c p).symm)
local instance openTower : IsScalarTower R (OpenOrder c) (L c):=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=OpenOrder c) (A:=L c)
    (fun p=>(SourceOpenFractionField318.openEmbedding_on_polynomial c p).symm)

/-- The source normalization's actual t-chart integral closure is computed
in the specified whole original function field. -/
theorem openClosure_isIntegralClosure :
    IsIntegralClosure (integralClosure R (OpenOrder c)) R (L c):=
  IsIntegralClosure.of_isIntegralClosure_of_isIntegrallyClosedIn
    R (integralClosure R (OpenOrder c)) (OpenOrder c) (L c)

/-- Once normality of the entire polynomial order is proved, its already
specified full fraction field identifies it as the entire integral closure. -/
theorem source_isIntegralClosure (hn:IsIntegrallyClosed (SourceOrder c)) :
    IsIntegralClosure (SourceOrder c) R (L c):=by
  letI:=hn
  constructor
  · exact embedding_injective c
  · intro x
    constructor
    · intro hx
      exact IsIntegrallyClosed.algebraMap_eq_of_integral (hx.tower_top : IsIntegral (SourceOrder c) x)
    · rintro ⟨y,rfl⟩
      exact (IsIntegral.of_finite R y).map (IsScalarTower.toAlgHom R (SourceOrder c) (L c))

@[expose] def sourceClosureEquiv (hn:IsIntegrallyClosed (SourceOrder c)) :
    integralClosure R (OpenOrder c)≃ₐ[R]SourceOrder c:=by
  letI:=openClosure_isIntegralClosure c
  letI:=source_isIntegralClosure c hn
  exact IsIntegralClosure.equiv R (integralClosure R (OpenOrder c)) (L c) (SourceOrder c)

theorem sourceClosureEquiv_embedding (hn:IsIntegrallyClosed (SourceOrder c))
    (x:integralClosure R (OpenOrder c)) :
    embedding c (sourceClosureEquiv c hn x)=SourceOpenFractionField318.openEmbedding c x.val:=by
  letI:=openClosure_isIntegralClosure c
  letI:=source_isIntegralClosure c hn
  exact IsIntegralClosure.algebraMap_equiv R (integralClosure R (OpenOrder c)) (L c) (SourceOrder c) x

@[expose] def chartRing : CommRingCat:=
  Γ((ContactProjectiveModel318.coverMap c).normalization,
    (ContactProjectiveModel318.coverMap c).fromNormalization⁻¹ᵁ(JLineAtlas318.chart ℚ 1 ''ᵁ ⊤))

@[expose] def actualChartEquiv (hn:IsIntegrallyClosed (SourceOrder c)) :
    chartRing c≃+*SourceOrder c:=
  (InfinityGlobalChart318.sectionsEquiv_of_factor
    (CommRingCat.ofHom (ContactGlobalProper318.finitePolynomial c)) (JLineAtlas318.chart ℚ 1)
    (ContactProjectiveModel318.coverMap c) (ContactGlobalProper318.finite_factor c)).trans
    (sourceClosureEquiv c hn).toRingEquiv
end SourceClosureComparison318
