module
public import FifthCharacterOrder318
public import SourceGlobalAffine318
public section
noncomputable section
namespace FifthCharacterSource318
open Polynomial SourceTwistArithmetic318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev R:=ℚ[X]
abbrev K:=RatFunc ℚ
abbrev Source:=ContactKummerOrder318.SourceOrder units
abbrev L:=KummerTensorField318.Raw (SourceKummerField318.parameter units)
abbrev Quartic:=FifthCharacterOrder318.Order

local instance sourceAlgebra : Algebra Source L:=(ContactKummerOrder318.embedding units).toAlgebra
local instance baseAlgebra : Algebra R L:=((algebraMap K L).comp (algebraMap R K)).toAlgebra
local instance baseSMul : SMul R L:=baseAlgebra.toSMul
local instance baseModule : Module R L:=Algebra.toModule
local instance sourceTower : IsScalarTower R Source L:=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=Source) (A:=L)
    (fun p=>(SourceFractionField318.embedding_on_polynomial units p).symm)
local instance sourceClosure : IsIntegralClosure Source R L:=
  SourceClosureComparison318.source_isIntegralClosure units (SourceGlobalAffine318.source_integrallyClosed units)
local instance quarticFinite:Module.Finite R (Quartic):=FourRootOrder318.root_finite _

@[expose] def toRaw:Quartic→+*L:=
  (FifthCharacterField318.field).subtype.comp (FifthCharacterOrder318.embedding)

lemma toRaw_on_polynomial (p:R):
    toRaw (algebraMap R (Quartic) p)=algebraMap R L p:=by
  exact congrArg (fun x:FifthCharacterOrder318.Field=>(x:L))
    (FifthCharacterOrder318.embedding_on_polynomial p)

local instance quarticAlgebra:Algebra (Quartic) L:=(toRaw).toAlgebra
local instance quarticTower:IsScalarTower R (Quartic) L:=
  IsScalarTower.of_algebraMap_eq (fun p=>(toRaw_on_polynomial p).symm)

/-- The actual quartic quotient functions extend regularly to the entire
original finite source chart, by its proved integral-closure property. -/
@[expose] def toSource:Quartic→ₐ[R]Source:=
  IsIntegralClosure.lift R Source L

theorem toSource_embedding (x:Quartic):
    ContactKummerOrder318.embedding units (toSource x)=toRaw x:=
  IsIntegralClosure.algebraMap_lift R Source L x

theorem toSource_injective:Function.Injective (toSource):=by
  intro x y h
  apply FifthCharacterOrder318.embedding_injective
  apply Subtype.ext
  exact (toSource_embedding x).symm.trans
    ((congrArg (ContactKummerOrder318.embedding units) h).trans (toSource_embedding y))

local instance sourceQuarticAlgebra:Algebra (Quartic) Source:=(toSource).toAlgebra
local instance sourceQuarticTower:IsScalarTower R (Quartic) Source:=
  IsScalarTower.of_algebraMap_eq (fun p=>(toSource).commutes p |>.symm)

theorem toSource_finite:(toSource).toRingHom.Finite:=by
  letI:= (ContactKummerOrder318.source_finite_free units).1
  exact Module.Finite.of_restrictScalars_finite R (Quartic) Source

theorem source_root_embedding :
    ContactKummerOrder318.embedding units
      (toSource (AdjoinRoot.root (QuadraticPresentation318.polynomial FifthCharacterPolynomial318.quartic)))=
    FifthCharacterField318.root := by
  rw [toSource_embedding]
  exact FifthCharacterOrder318.embedding_root
end FifthCharacterSource318
