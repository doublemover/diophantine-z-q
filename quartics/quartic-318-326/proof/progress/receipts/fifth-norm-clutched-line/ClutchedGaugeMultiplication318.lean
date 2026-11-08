module
public import ClutchedModule318
public section
noncomputable section
namespace ClutchedGaugeMultiplication318
open AlgebraicGeometry CategoryTheory Opposite
open ClutchedModule318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
lemma multiply_comp {X:Scheme.{u}} (a b:Γ(X,⊤)):
    multiply a≫multiply b=multiply (a*b):=by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (multiply b).app U ((multiply a).app U x)=(multiply (a*b)).app U x
  simp only [multiply_apply,map_mul,mul_assoc]
variable {X Y Z:Scheme.{u}} (j:Y⟶X) (k:Z⟶Y)
lemma restriction_multiply (a:Γ(Y,⊤)):
    (Scheme.Modules.pushforward j).map (multiply a)≫restriction j k=
      restriction j k≫(Scheme.Modules.pushforward (k≫j)).map (multiply (k.appTop a)):=by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change k.app (j⁻¹ᵁU) ((multiply a).app (j⁻¹ᵁU) x)=
    (multiply (k.appTop a)).app (k⁻¹ᵁ(j⁻¹ᵁU)) (k.app (j⁻¹ᵁU) x)
  rw [multiply_apply,multiply_apply,map_mul]
  congr 1
  exact congrArg (fun f=>f a) (k.naturality (homOfLE (show j⁻¹ᵁU≤⊤ from le_top)).op)
variable {Y₀ Y₁ W:Scheme.{u}}
  (j₀:Y₀⟶X) (j₁:Y₁⟶X) (k₀:W⟶Y₀) (k₁:W⟶Y₁)
  (h:k₁≫j₁=k₀≫j₀)
/-- Exact second square for changing both actual local coefficient frames. -/
lemma second_square (a b c:Γ(W,⊤)) (s:Γ(Y₁,⊤)) (he:k₁.appTop s*b=a*c):
    (Scheme.Modules.pushforward j₁).map (multiply s)≫twistedRestriction j₀ j₁ k₀ k₁ h b=
      twistedRestriction j₀ j₁ k₀ k₁ h a≫
        (Scheme.Modules.pushforward (k₀≫j₀)).map (multiply c):=by
  unfold twistedRestriction
  rw [←Category.assoc,←Category.assoc,restriction_multiply,
    Category.assoc,Category.assoc]
  rw [←Category.assoc ((Scheme.Modules.pushforward (k₁≫j₁)).map (multiply (k₁.appTop s)))
    ((Scheme.Modules.pushforwardCongr h).hom.app (unit W)),
    (Scheme.Modules.pushforwardCongr h).hom.naturality (multiply (k₁.appTop s))]
  simp only [Category.assoc,←Functor.map_comp,multiply_comp,he]
end ClutchedGaugeMultiplication318
