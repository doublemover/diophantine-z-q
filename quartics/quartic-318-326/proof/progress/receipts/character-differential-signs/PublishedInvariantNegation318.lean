module
public import WeierstrassGlobalNegation318
public import ContactCharacterDifferentials318
public import CharacterBooleanGlobal318
public section
noncomputable section
namespace PublishedInvariantNegation318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The actual published y coordinate is nonzero, by its fixed original
contact-field embedding and already proved complementary-root nonvanishing. -/
theorem y_ne_zero (i:Fin 4):
    ShortAffineJacobian318.y (publishedA i) (publishedB i)≠0:=by
  intro h
  have he:=congrArg (CompletedCharacterInfinity318.rawMap i) h
  rw [map_zero] at he
  exact CompletedCharacterInfinity318.rawY_ne_zero i he

theorem two_y_ne_zero (i:Fin 4):
    (2:ShortAffineJacobian318.Ring (publishedA i) (publishedB i))*
      ShortAffineJacobian318.y (publishedA i) (publishedB i)≠0:=by
  letI:=AffineCoordinateDomain318.affine_domain (publishedA i) (publishedB i)
  letI:CharZero (ShortAffineJacobian318.Ring (publishedA i) (publishedB i)):=
    Algebra.charZero_of_charZero ℚ _
  exact mul_ne_zero (by norm_num) (y_ne_zero i)

/-- No target involution convention is suppressed: this is the actual
whole-Scheme (x,y) -> (x,-y) involution and the actual dx/(2y) generator. -/
theorem invariant_negation (i:Fin 4):
    IntrinsicDifferentialPullback318.globalSection
      (GluedNegation318.negation (publishedA i) (publishedB i))
      (WeierstrassGluing318.structureMap (publishedA i) (publishedB i))
      (WeierstrassGluing318.structureMap (publishedA i) (publishedB i))
      (GluedNegation318.negation_over_base (publishedA i) (publishedB i))
      (ContactCharacterDifferentials318.invariant i)= -ContactCharacterDifferentials318.invariant i:=
  WeierstrassGlobalNegation318.global _ _ (ContactCharacterDifferentials318.discriminantUnit i)
    (two_y_ne_zero i)
end PublishedInvariantNegation318
