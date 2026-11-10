module
public import MixedCoverCompatibleRecovery318
public section
noncomputable section
namespace RefinementDoubleCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ActualOverlapDiagram318
open ActualDescentBaseChangeDiagram318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y V : Scheme.{u}} (f : X ⟶ Y) (p : V ⟶ X)
abbrev refined : V ⟶ Y := p ≫ f
lemma square : p ≫ f = refined f p ≫ 𝟙 Y := (Category.comp_id _).symm
abbrev double : Double (refined f p) ⟶ Double f := doubleMap f (refined f p) p (𝟙 Y) (square f p)
abbrev middle := pullback (first f) p
abbrev projection : middle f p ⟶ Double f := pullback.fst (first f) p
abbrev liftFirst : middle f p ⟶ V := pullback.snd (first f) p

@[expose] def toMiddle : Double (refined f p) ⟶ middle f p :=
  pullback.lift (double f p) (first (refined f p)) (double_first f (refined f p) p (𝟙 Y) (square f p))
@[reassoc] lemma toMiddle_projection : toMiddle f p ≫ projection f p = double f p := pullback.lift_fst _ _ _
@[reassoc] lemma toMiddle_first : toMiddle f p ≫ liftFirst f p = first (refined f p) := pullback.lift_snd _ _ _

/-- Refining both endpoints factors the map of original doubles into
two genuine base changes of p. The middle object retains the first lift. -/
lemma cartesian : IsPullback (toMiddle f p) (second (refined f p))
    (projection f p ≫ second f) p := by
  apply IsPullback.mk'
  · rw [← Category.assoc,toMiddle_projection,double_second]
  · intro T x y hx hy
    apply pullback.hom_ext
    · have h := congrArg (fun z => z ≫ liftFirst f p) hx
      simpa only [Category.assoc,toMiddle_first] using h
    · exact hy
  · intro T x y hxy
    have hx : (x ≫ liftFirst f p) ≫ p = (x ≫ projection f p) ≫ first f := by
      simpa only [Category.assoc] using congrArg (fun t => x ≫ t)
        (pullback.condition (f:=first f) (g:=p)).symm
    have hy : (x ≫ projection f p) ≫ second f = y ≫ p := by
      simpa only [Category.assoc] using hxy
    have he : (x ≫ liftFirst f p) ≫ refined f p = y ≫ refined f p := by
      calc
        _ = ((x ≫ liftFirst f p) ≫ p) ≫ f := (Category.assoc _ _ _).symm
        _ = ((x ≫ projection f p) ≫ first f) ≫ f := congrArg (fun t => t ≫ f) hx
        _ = ((x ≫ projection f p) ≫ second f) ≫ f := by
          rw [Category.assoc,edge_condition,Category.assoc]
        _ = (y ≫ p) ≫ f := congrArg (fun t => t ≫ f) hy
        _ = _ := Category.assoc _ _ _
    let z := pullback.lift (x ≫ liftFirst f p) y he
    refine ⟨z,?_,pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · rw [Category.assoc,toMiddle_projection]
      apply pullback.hom_ext
      · rw [Category.assoc,double_first,← Category.assoc,pullback.lift_fst]
        simpa only [Category.assoc] using congrArg (fun t => x ≫ t) (pullback.condition (f:=first f) (g:=p)).symm
      · rw [Category.assoc,double_second,← Category.assoc,pullback.lift_snd]
        exact hxy.symm
    · rw [Category.assoc,toMiddle_first]
      exact pullback.lift_fst _ _ _

variable [IsAffineHom p] [Flat p] [Surjective p]
instance toMiddle_affine : IsAffineHom (toMiddle f p) :=
  MorphismProperty.of_isPullback (cartesian f p).flip (inferInstance : IsAffineHom p)
instance toMiddle_flat : Flat (toMiddle f p) :=
  MorphismProperty.of_isPullback (cartesian f p).flip (inferInstance : Flat p)
instance toMiddle_surjective : Surjective (toMiddle f p) :=
  MorphismProperty.of_isPullback (cartesian f p).flip (inferInstance : Surjective p)

instance double_affine : IsAffineHom (double f p) := by
  rw [← toMiddle_projection]
  infer_instance
instance double_flat : Flat (double f p) := by
  rw [← toMiddle_projection]
  infer_instance
instance double_surjective : Surjective (double f p) := by
  rw [← toMiddle_projection]
  infer_instance
end RefinementDoubleCover318
