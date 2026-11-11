module
public import RefinedCoverFaithfulness318
public section
noncomputable section
namespace MixedCoverRecovery318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open OriginalSchemeDescentData318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
  [IsAffineHom g] [Flat g] [Surjective g] (a : U ⟶ X) (factor : a ≫ f = g)
  (D : Datum f)
abbrev mixed := pullback f g
abbrev first : mixed f g ⟶ X := pullback.fst f g
abbrev second : mixed f g ⟶ U := pullback.snd f g
lemma square : first f g ≫ f = second f g ≫ g := pullback.condition
include factor in
lemma pair_condition : first f g ≫ f = (second f g ≫ a) ≫ f := by
  rw [Category.assoc,factor,square]

@[expose] def restricted : Datum g :=
  OriginalSchemeDescentBaseChange318.datum f g a (𝟙 Y) (by rw [factor,Category.comp_id]) D
abbrev baseLine := AffineGlobalMorphismEffectivity318.line g (restricted f g a factor D)
abbrev reconstruction := AffineMorphismGlobalRecovery318.comparison g (restricted f g a factor D)

/-- On the entire mixed fiber product, the reconstruction from the
refinement agrees with the original covering line. Its final arrow is
the inverse of the original overlap evaluated on the actual mixed pair. -/
@[expose] def comparison :
    (Scheme.Modules.pullback (first f g)).obj ((Scheme.Modules.pullback f).obj (baseLine f g a factor D).object) ≅
      (Scheme.Modules.pullback (first f g)).obj D.line.object :=
  (ActualDescentBaseChangeDiagram318.coverComparison f (second f g) (first f g) g (square f g)).app
      (baseLine f g a factor D).object ≪≫
    (Scheme.Modules.pullback (second f g)).mapIso (reconstruction f g a factor D) ≪≫
      (PullbackPathComposition318.iso (second f g) a (second f g ≫ a) rfl).app D.line.object ≪≫
        (ActualDescentTestEvaluation318.iso D (first f g) (second f g ≫ a)
          (pair_condition f g a factor)).symm

/-- The mixed cover of the entire original covering scheme has all
three needed hypotheses, derived from the genuine pullback square. -/
instance mixed_affine : IsAffineHom (first f g) := inferInstance
instance mixed_flat : Flat (first f g) := inferInstance
instance mixed_surjective : Surjective (first f g) := inferInstance
end MixedCoverRecovery318
