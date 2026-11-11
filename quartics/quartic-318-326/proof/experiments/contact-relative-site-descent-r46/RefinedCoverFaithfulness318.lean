module
public import ActualDescentEvaluationNaturality318
public section
noncomputable section
namespace RefinedCoverFaithfulness318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)

include factor in
/-- An arbitrary covering arrow is faithful on original line maps as
soon as it has the displayed affine faithfully flat refinement. -/
lemma pullback_injective {L K : Line Y} (h k : L.object ⟶ K.object)
    (he : (Scheme.Modules.pullback f).map h = (Scheme.Modules.pullback f).map k) : h = k := by
  let c := PullbackPathComposition318.iso a f g factor
  have ha := congrArg (Scheme.Modules.pullback a).map he
  apply GlobalAffineLineFaithfulness318.pullback_injective g
  apply (cancel_epi (c.hom.app L.object)).mp
  rw [← c.hom.naturality h,← c.hom.naturality k]
  exact congrArg (fun t => t ≫ c.hom.app K.object) ha
end RefinedCoverFaithfulness318
