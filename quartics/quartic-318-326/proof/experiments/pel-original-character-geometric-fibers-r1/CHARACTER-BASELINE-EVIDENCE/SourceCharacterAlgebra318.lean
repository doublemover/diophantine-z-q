module
public import CubicCharacterFraction318
public import CubicPublishedScheme318
public import SourceGlobalAffine318
public section
noncomputable section
namespace SourceCharacterAlgebra318
open Polynomial SourceTwistArithmetic318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev R:=ℚ[X]
abbrev K:=RatFunc ℚ
abbrev Source:=ContactKummerOrder318.SourceOrder units
abbrev L:=KummerTensorField318.Raw (SourceKummerField318.parameter units)
abbrev Cubic (i:Fin 4):=CubicCharacterFraction318.Order i

local instance sourceAlgebra : Algebra Source L:=(ContactKummerOrder318.embedding units).toAlgebra
local instance baseAlgebra : Algebra R L:=((algebraMap K L).comp (algebraMap R K)).toAlgebra
local instance baseSMul : SMul R L:=baseAlgebra.toSMul
local instance baseModule : Module R L:=Algebra.toModule
local instance sourceTower : IsScalarTower R Source L:=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=Source) (A:=L)
    (fun p=>(SourceFractionField318.embedding_on_polynomial units p).symm)
local instance sourceClosure : IsIntegralClosure Source R L:=
  SourceClosureComparison318.source_isIntegralClosure units (SourceGlobalAffine318.source_integrallyClosed units)
local instance cubicFinite (i:Fin 4):Module.Finite R (Cubic i):=FourRootOrder318.root_finite _

@[expose] def toRaw (i:Fin 4):Cubic i→+*L:=
  (SourceCharacterFields318.field units i).subtype.comp (CubicCharacterFraction318.embedding i)

lemma toRaw_on_polynomial (i:Fin 4) (p:R):
    toRaw i (algebraMap R (Cubic i) p)=algebraMap R L p:=by
  exact congrArg (fun x:CubicCharacterFraction318.Field i=>(x:L))
    (CubicCharacterFraction318.embedding_on_polynomial i p)

local instance cubicAlgebra (i:Fin 4):Algebra (Cubic i) L:=(toRaw i).toAlgebra
local instance cubicTower (i:Fin 4):IsScalarTower R (Cubic i) L:=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=Cubic i) (A:=L)
    (fun p=>(toRaw_on_polynomial i p).symm)

/-- The actual cubic quotient functions extend regularly to the entire
original finite source chart, by its proved integral-closure property. -/
@[expose] def toSource (i:Fin 4):Cubic i→ₐ[R]Source:=
  IsIntegralClosure.lift R Source L

theorem toSource_embedding (i:Fin 4) (x:Cubic i):
    ContactKummerOrder318.embedding units (toSource i x)=toRaw i x:=
  IsIntegralClosure.algebraMap_lift R Source L x

theorem toSource_injective (i:Fin 4):Function.Injective (toSource i):=by
  intro x y h
  apply CubicCharacterFraction318.embedding_injective i
  apply Subtype.ext
  exact (toSource_embedding i x).symm.trans
    ((congrArg (ContactKummerOrder318.embedding units) h).trans (toSource_embedding i y))

local instance sourceCubicAlgebra (i:Fin 4):Algebra (Cubic i) Source:=(toSource i).toAlgebra
local instance sourceCubicTower (i:Fin 4):IsScalarTower R (Cubic i) Source:=
  IsScalarTower.of_algebraMap_eq (R:=R) (S:=Cubic i) (A:=Source)
    (fun p=>(toSource i).commutes p |>.symm)

theorem toSource_finite (i:Fin 4):(toSource i).toRingHom.Finite:=by
  letI:= (ContactKummerOrder318.source_finite_free units).1
  exact Module.Finite.of_restrictScalars_finite R (Cubic i) Source

/-- The specified actual published coordinate functions are regular on the
whole finite source chart, with no arbitrary abstract field identification. -/
@[expose] def publishedToSource (i:Fin 4):
    ShortAffineJacobian318.Ring (publishedA i) (publishedB i)→ₐ[ℚ]Source:=
  (toSource i).restrictScalars ℚ |>.comp (CubicPublishedScheme318.coordinateEquiv i).symm.toAlgHom

theorem publishedToSource_finite (i:Fin 4):(publishedToSource i).toRingHom.Finite:=
  (toSource_finite i).comp (RingHom.Finite.of_surjective _
    (CubicPublishedScheme318.coordinateEquiv i).symm.surjective)

theorem publishedToSource_injective (i:Fin 4):Function.Injective (publishedToSource i):=
  (toSource_injective i).comp (CubicPublishedScheme318.coordinateEquiv i).symm.injective
end SourceCharacterAlgebra318
