module
public import SourceFinitePointLift318
public section
noncomputable section
namespace ContactBranchStabilizer318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318 Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ) (i:Fin 4) {F:Type} [Field F] [Algebra ℚ F]
/-- Evaluation at the actual labelled contact in the original t-line. -/
@[expose] def contactHom:R→+*F:=
  (Polynomial.aeval (algebraMap ℚ F (LinearContactSquareclass318.contacts i))).toRingHom
@[expose] def contactPoint:Spec (CommRingCat.of F)⟶ProjectiveJLine318.scheme ℚ:=
  Spec.map (CommRingCat.ofHom (contactHom (F:=F) i))≫JLineAtlas318.chart ℚ 1
variable (q:Spec (CommRingCat.of F)⟶ContactProjectiveModel318.model c)
    (hq:q≫ContactProjectiveModel318.modelMap c=contactPoint (F:=F) i)
include hq
/-- For every field-valued point of the actual projective source above a
finite contact, exactly the identity and that contact's single root flip
stabilize it. No chosen affine presentation or algebra structure is assumed. -/
theorem fixed_exactly (b:Fin 4→Bool):q≫ContactGlobalSigns318.map c b=q↔
    b=(fun _=>false)∨b=SourceCharacterFields318.flip i:=by
  letI:Algebra R F:=(contactHom (F:=F) i).toAlgebra
  letI:IsScalarTower ℚ R F:=by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap ℚ F a=Polynomial.aeval
      (algebraMap ℚ F (LinearContactSquareclass318.contacts i)) (C a)
    exact (Polynomial.aeval_C _ _).symm
  have ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i):=
    Polynomial.aeval_X _
  exact SourceFinitePointLift318.stabilizer_exactly c q hq i ht b
/-- Two distinct actual whole-source maps stabilize each actual geometric
branch point. This counts point stabilizers, not the nonreduced fiber action. -/
theorem stabilizer_image_card:Nat.card (Set.range
    (fun b:{b:Fin 4→Bool // q≫ContactGlobalSigns318.map c b=q}=>ContactGlobalSigns318.map c b.val))=2:=by
  letI:Algebra R F:=(contactHom (F:=F) i).toAlgebra
  letI:IsScalarTower ℚ R F:=by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap ℚ F a=Polynomial.aeval
      (algebraMap ℚ F (LinearContactSquareclass318.contacts i)) (C a)
    exact (Polynomial.aeval_C _ _).symm
  have ht:algebraMap R F X=algebraMap ℚ F (LinearContactSquareclass318.contacts i):=
    Polynomial.aeval_X _
  exact SourceFinitePointLift318.stabilizer_image_card c q hq i ht
end ContactBranchStabilizer318
