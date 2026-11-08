module
public import ClutchedGaugeMultiplication318
public section
noncomputable section
namespace ClutchedGaugeIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ClutchedModule318 ClutchedGaugeMultiplication318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y₀ Y₁ W:Scheme.{u}}
  (j₀:Y₀⟶X) (j₁:Y₁⟶X) (k₀:W⟶Y₀) (k₁:W⟶Y₁)
  (h:k₁≫j₁=k₀≫j₀) (a b:Γ(W,⊤)) (s₀:Γ(Y₀,⊤)ˣ) (s₁:Γ(Y₁,⊤)ˣ)
  (he:k₁.appTop s₁.val*b=a*k₀.appTop s₀.val)
/-- Genuine change of frame on the categorical pullback module sheaves. -/
@[expose] def map:sheaf j₀ j₁ k₀ k₁ h a⟶sheaf j₀ j₁ k₀ k₁ h b:=
  pullback.map (restriction j₀ k₀) (twistedRestriction j₀ j₁ k₀ k₁ h a)
    (restriction j₀ k₀) (twistedRestriction j₀ j₁ k₀ k₁ h b)
    ((Scheme.Modules.pushforward j₀).map (multiply s₀.val))
    ((Scheme.Modules.pushforward j₁).map (multiply s₁.val))
    ((Scheme.Modules.pushforward (k₀≫j₀)).map (multiply (k₀.appTop s₀.val)))
    (restriction_multiply j₀ k₀ s₀.val).symm
    (second_square j₀ j₁ k₀ k₁ h a b (k₀.appTop s₀.val) s₁.val he).symm
lemma map_isIso:IsIso (map j₀ j₁ k₀ k₁ h a b s₀ s₁ he):=by
  letI:=multiply_isIso s₀.val s₀.isUnit
  letI:=multiply_isIso s₁.val s₁.isUnit
  letI:=multiply_isIso (k₀.appTop s₀.val) (s₀.isUnit.map k₀.appTop.hom)
  unfold map
  infer_instance
@[expose] def iso:sheaf j₀ j₁ k₀ k₁ h a≅sheaf j₀ j₁ k₀ k₁ h b:=by
  letI:=map_isIso j₀ j₁ k₀ k₁ h a b s₀ s₁ he
  exact asIso (map j₀ j₁ k₀ k₁ h a b s₀ s₁ he)
lemma first_map:map j₀ j₁ k₀ k₁ h a b s₀ s₁ he≫first j₀ j₁ k₀ k₁ h b=
    first j₀ j₁ k₀ k₁ h a≫(Scheme.Modules.pushforward j₀).map (multiply s₀.val):=
  pullback.lift_fst ..
lemma second_map:map j₀ j₁ k₀ k₁ h a b s₀ s₁ he≫second j₀ j₁ k₀ k₁ h b=
    second j₀ j₁ k₀ k₁ h a≫(Scheme.Modules.pushforward j₁).map (multiply s₁.val):=
  pullback.lift_snd ..
end ClutchedGaugeIso318
