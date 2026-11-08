module
public import ThreeTorsionDiamond318
public import LiteralThreeTorsion318
public import PrimitivePointedModel318
public section
noncomputable section
namespace PrimitiveThreeModel318
open PrimitiveDiamond318 InvariantBaseChange318
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev Base:=OpenJModel318.Base 3
abbrev Cover:=LiteralThreeTorsion318.Ring 3
abbrev SplitRing:=ThreeTorsionSplitData318.T (OpenJAffineScheme318.A 3)
  (OpenJAffineScheme318.B 3) (OpenJAffineScheme318.discriminant_unit 3)

@[expose] def splitEquiv : SplitRing⊗[Base]Cover≃ₐ[SplitRing](Points 3→SplitRing) :=
  ThreeTorsionDiamond318.primitiveSplit _ _ _
@[expose] def action (H:Subgroup (ZMod 3)ˣ) : H→Cover≃ₐ[Base]Cover :=
  fun g=>ThreeTorsionDiamond318.diamond _ _ _ g.val

theorem equivariant (H:Subgroup (ZMod 3)ˣ) :
    ∀(g:H)(b:SplitRing⊗[Base]Cover)(p:Points 3),
      splitEquiv (baseAction SplitRing (action H) g b) p=splitEquiv b (g•p) :=
  fun g b p=>ThreeTorsionDiamond318.equivariant _ _ _ g.val b p

/-- The actual primitive-three cover supplies its own faithfully-flat
finite-etale splitting and actual coordinate diamond action. -/
@[expose] def pointedComponent (Ω:Type) [Field Ω] (H:Subgroup (ZMod 3)ˣ)
    (β:Cover→+*Ω) :=
  PrimitivePointedModel318.component 3 Cover SplitRing Ω H (action H) splitEquiv
    (equivariant H) β

theorem proper_model (Ω:Type) [Field Ω] (H:Subgroup (ZMod 3)ˣ) (β:Cover→+*Ω) :
    let c:=pointedComponent Ω H β
    AlgebraicGeometry.IsProper (PointedArithmeticModel318.structureMap c) ∧
      AlgebraicGeometry.Flat (PointedArithmeticModel318.structureMap c) ∧
      AlgebraicGeometry.Surjective (PointedArithmeticModel318.structureMap c) :=
  PointedArithmeticModel318.proper_flat_surjective _ (by decide)

end PrimitiveThreeModel318
