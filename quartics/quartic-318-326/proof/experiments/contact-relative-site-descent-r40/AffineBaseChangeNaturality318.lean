module
public import AffineReconstructionBaseChange318
public section
noncomputable section
namespace AffineBaseChangeNaturality318
open AlgebraicGeometry CategoryTheory
open ActualAffineDescentData318 ActualAffineDoubleNerve318 AffineReconstructionBaseChange318
set_option maxHeartbeats 2000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S R' S' : CommRingCat.{u}) [Algebra R S] [Algebra R' S']
  [Module.FaithfullyFlat R S] [Module.FaithfullyFlat R' S']
  (a : Spec S' ⟶ Spec S) (b : Spec R' ⟶ Spec R)
  (square : a ≫ baseMap R S = baseMap R' S' ≫ b)

/-- The exact changed-reconstruction comparison is natural for every
original compatible covering map. This follows from its proved covering
equation and the original morphism reconstruction squares. -/
lemma comparison_natural {D E : Datum R S} (h : Hom D E) :
    (Scheme.Modules.pullback b).map (ActualAffineDescendedMaps318.map h) ≫
        (comparison R S R' S' a b square E).hom =
      (comparison R S R' S' a b square D).hom ≫
        ActualAffineDescendedMaps318.map (AffineChangedBaseEffectivity318.map R S R' S' a b square h) := by
  let m := ActualAffineDescendedMaps318.map h
  let n := ActualAffineDescendedMaps318.map (AffineChangedBaseEffectivity318.map R S R' S' a b square h)
  let P := Scheme.Modules.pullback (baseMap R' S')
  have hn := (ActualDescentBaseChangeDiagram318.coverComparison
    (baseMap R S) (baseMap R' S') a b square).inv.naturality m
  change P.map ((Scheme.Modules.pullback b).map m) ≫ (coverPath R S R' S' a b square E).inv =
    (coverPath R S R' S' a b square D).inv ≫
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback (baseMap R S)).map m) at hn
  apply OriginalAffineLineFaithfulness318.maps_eq_of_cover_square R' S' _ _
    (changedComparison R S R' S' a b square E)
  simp only [Functor.map_comp, Category.assoc]
  rw [comparison_cover, ActualAffineDescendedMaps318.map_commutes]
  rw [← Category.assoc (P.map (comparison R S R' S' a b square D).hom), comparison_cover]
  rw [← Category.assoc (P.map ((Scheme.Modules.pullback b).map m)), hn, Category.assoc,
    ← Functor.map_comp, ActualAffineDescendedMaps318.map_commutes, Functor.map_comp,
    Category.assoc]
end AffineBaseChangeNaturality318
