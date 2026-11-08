module
public import LiteralSchemePointGroup318
public section
noncomputable section
namespace LiteralTriplingNegation318
open AlgebraicGeometry CategoryTheory
open LiteralSchemePointOperations318 LiteralSchemeCancellation318 LiteralSchemePointGroup318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Actual global Scheme-map commutation, obtained from the represented group
operations on the universal test map, not from field-valued points. -/
theorem commute (N:ℕ) :
    GluedNegation318.negation (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) ≫
      CompletedIteratedAddition318.tripling (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
        (OpenJAffineScheme318.discriminant_unit N)=
    CompletedIteratedAddition318.tripling (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
        (OpenJAffineScheme318.discriminant_unit N) ≫
      GluedNegation318.negation (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) := by
  let b:=WeierstrassGluing318.structureMap (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)
  let p:Points N b:=⟨𝟙 _,Category.id_comp _⟩
  have h:=congrArg Subtype.val (neg_triple N b p)
  simpa only [neg,triple_value,p,Category.id_comp,Category.assoc] using h.symm
end LiteralTriplingNegation318
