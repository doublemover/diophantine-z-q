module
public import RefinedCoverObjectEffectivity318
public section
noncomputable section
namespace RefinementDescentFaithfulness318
open AlgebraicGeometry CategoryTheory
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318 MixedCoverRecovery318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)
  {D E : Datum f}

include factor in
/-- A compatible covering map is determined by its restriction to the
specified refinement, even though a itself need not be a cover of X. -/
lemma hom_ext (h k : Hom D E)
    (he : (Scheme.Modules.pullback a).map h.sheafHom = (Scheme.Modules.pullback a).map k.sheafHom) : h = k := by
  let p := first f g
  let q := second f g
  let c := PullbackPathComposition318.iso q a (q ≫ a) rfl
  have heq : (Scheme.Modules.pullback (q ≫ a)).map h.sheafHom =
      (Scheme.Modules.pullback (q ≫ a)).map k.sheafHom := by
    apply (cancel_epi (c.hom.app D.line.object)).mp
    rw [← c.hom.naturality h.sheafHom,← c.hom.naturality k.sheafHom]
    exact congrArg (fun t => (Scheme.Modules.pullback q).map t ≫ c.hom.app E.line.object) he
  apply Hom.ext
  apply GlobalAffineLineFaithfulness318.pullback_injective p (L:=D.line) (K:=E.line)
  let e := ActualDescentTestEvaluation318.iso E p (q ≫ a) (pair_condition f g a factor)
  apply (cancel_mono e.hom).mp
  rw [← ActualDescentEvaluationNaturality318.natural p (q ≫ a) (pair_condition f g a factor) h,
    ← ActualDescentEvaluationNaturality318.natural p (q ≫ a) (pair_condition f g a factor) k,heq]

lemma map_injective : Function.Injective
    (OriginalSchemeDescentBaseChangeMaps318.map g a (𝟙 Y) (by rw [factor,Category.comp_id])
      (D:=D) (E:=E)) := by
  intro h k he
  exact hom_ext f g a factor h k (congrArg Hom.sheafHom he)
end RefinementDescentFaithfulness318
