module
public import FifthCompletedGlobal318
public import FifthOverlapDifferentialEquation318
public import IntrinsicDifferentialSectionPullback318
public section
noncomputable section
namespace FifthActualDifferential318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthCharacterShortPolynomial318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev M:=ContactIntrinsicDifferentials318.omega units
@[expose] def invariant:=IntrinsicGlobalFrame318.invariant A B discriminant_unit
@[expose] def differential:Γ(M,⊤):=
  IntrinsicDifferentialPullback318.globalSection FifthCompletedGlobal318.map
    (ContactIntrinsicDifferentials318.structureMap units)
    (WeierstrassGluing318.structureMap A B) FifthCompletedGlobal318.over_Q invariant
/-- Literal entire common-open square for the now checked completed fifth map. -/
theorem on_common:ContactOverlapIntrinsic318.embedding units≫FifthCompletedGlobal318.map=
    Spec.map (CommRingCat.ofHom FifthSourceOverlap318.shortMap.toRingHom)≫
      WeierstrassGluing318.finiteChart A B:=by
  change ContactProjectiveModel318.sourceOpen units≫FifthCompletedGlobal318.map=_
  rw [←ContactOverlapMaps318.source_square,Category.assoc,
    FifthCompletedGlobal318.on_finite,FifthSourceOverlap318.finite_restriction]
end FifthActualDifferential318
