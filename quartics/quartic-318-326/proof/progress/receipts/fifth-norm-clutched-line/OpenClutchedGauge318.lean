module
public import OpenClutchedTrivialization318
public import ClutchedGaugeIso318
public section
noncomputable section
namespace OpenClutchedGauge318
open AlgebraicGeometry CategoryTheory Opposite
open OpenClutchedLine318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (U V:X.Opens) (a b:Γ(X,U⊓V)ˣ)
  (s₀:Γ(X,U)ˣ) (s₁:Γ(X,V)ˣ)
  (he:X.presheaf.map (homOfLE (show U⊓V≤V from inf_le_right)).op s₁.val*b.val=
    a.val*X.presheaf.map (homOfLE (show U⊓V≤U from inf_le_left)).op s₀.val)
@[expose] def leftUnit:Γ(U.toScheme,⊤)ˣ:=Units.map U.topIso.inv.hom.toMonoidHom s₀
@[expose] def rightUnit:Γ(V.toScheme,⊤)ˣ:=Units.map V.topIso.inv.hom.toMonoidHom s₁
include he in
lemma compatible:
    (rightInclusion U V).appTop (rightUnit V s₁).val*transition U V b=
      transition U V a*(leftInclusion U V).appTop (leftUnit U s₀).val:=by
  change (rightInclusion U V).appTop (V.topIso.inv s₁.val)*transition U V b=
    transition U V a*(leftInclusion U V).appTop (U.topIso.inv s₀.val)
  rw [leftInclusion,rightInclusion,OpenClutchedTrivialization318.topIso_restrict,
    OpenClutchedTrivialization318.topIso_restrict]
  change (U⊓V: X.Opens).topIso.inv _ * (U⊓V: X.Opens).topIso.inv _=
    (U⊓V: X.Opens).topIso.inv _ * (U⊓V: X.Opens).topIso.inv _
  rw [←map_mul,←map_mul,he]
/-- The actual module-sheaf isomorphism corresponding to the specified
change of its two original frames. Both inverse laws come from the
categorical pullback map with invertible component maps. -/
@[expose] def iso:line U V a≅line U V b:=
  ClutchedGaugeIso318.iso U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a) (transition U V b)
    (leftUnit U s₀) (rightUnit V s₁) (compatible U V a b s₀ s₁ he)
lemma first_hom:(iso U V a b s₀ s₁ he).hom≫
    ClutchedModule318.first U.ι V.ι (leftInclusion U V) (rightInclusion U V)
      (square U V) (transition U V b)=
    ClutchedModule318.first U.ι V.ι (leftInclusion U V) (rightInclusion U V)
      (square U V) (transition U V a)≫
        (Scheme.Modules.pushforward U.ι).map (ClutchedModule318.multiply (leftUnit U s₀).val):=
  ClutchedGaugeIso318.first_map U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a) (transition U V b)
    (leftUnit U s₀) (rightUnit V s₁) (compatible U V a b s₀ s₁ he)
lemma second_hom:(iso U V a b s₀ s₁ he).hom≫
    ClutchedModule318.second U.ι V.ι (leftInclusion U V) (rightInclusion U V)
      (square U V) (transition U V b)=
    ClutchedModule318.second U.ι V.ι (leftInclusion U V) (rightInclusion U V)
      (square U V) (transition U V a)≫
        (Scheme.Modules.pushforward V.ι).map (ClutchedModule318.multiply (rightUnit V s₁).val):=
  ClutchedGaugeIso318.second_map U.ι V.ι (leftInclusion U V) (rightInclusion U V)
    (square U V) (transition U V a) (transition U V b)
    (leftUnit U s₀) (rightUnit V s₁) (compatible U V a b s₀ s₁ he)
end OpenClutchedGauge318
