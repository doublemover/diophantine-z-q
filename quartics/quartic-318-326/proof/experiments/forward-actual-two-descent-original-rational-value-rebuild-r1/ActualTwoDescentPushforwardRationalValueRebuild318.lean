module
public import ActualTwoDescentOpenRationalEvaluationRebuild318
public section
noncomputable section
namespace ActualTwoDescentPushforwardRationalValueRebuild318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules)
  (f : M ⟶ (Scheme.Modules.pushforward j).obj (ClutchedModule318.unit Y))

/-- A genuine all-nonempty-open rational value, from a specified native
pushforward morphism. This definition alone does not assert injectivity. -/
def value (U : X.Opens) [Nonempty U] (s : Γ(M,U)) : X.functionField :=
  ActualTwoDescentOpenRationalEvaluationRebuild318.evaluation j U (f.app U s)

lemma add (U : X.Opens) [Nonempty U] (s t : Γ(M,U)) :
    value j M f U (s+t)=value j M f U s+value j M f U t := by
  simp only [value,map_add]

lemma scalar (U : X.Opens) [Nonempty U] (a : Γ(X,U)) (s : Γ(M,U)) :
    value j M f U (a • s)=X.germToFunctionField U a*value j M f U s := by
  have hs := Scheme.Modules.Hom.app_smul f a s
  change f.app U (a • s)=j.app U a*f.app U s at hs
  unfold value
  rw [hs,map_mul,ActualTwoDescentOpenRationalEvaluationRebuild318.ambient]

lemma restrict (U V : X.Opens) [Nonempty U] [Nonempty V] (h : V ≤ U)
    (s : Γ(M,U)) :
    value j M f V (M.presheaf.map (homOfLE h).op s)=value j M f U s := by
  have hn := PresheafOfModules.naturality_apply f.val (homOfLE h).op s
  change f.app V (M.presheaf.map (homOfLE h).op s)=
    Y.presheaf.map (homOfLE (show j ⁻¹ᵁ V ≤ j ⁻¹ᵁ U from fun x hx => h hx)).op
      (f.app U s) at hn
  unfold value
  rw [hn]
  exact ActualTwoDescentOpenRationalEvaluationRebuild318.restrict j U V h _

lemma eq_iff (U : X.Opens) [Nonempty U] (s t : Γ(M,U)) :
    value j M f U s=value j M f U t ↔ f.app U s=f.app U t :=
  (ActualTwoDescentOpenRationalEvaluationRebuild318.injective j U).eq_iff
end ActualTwoDescentPushforwardRationalValueRebuild318
