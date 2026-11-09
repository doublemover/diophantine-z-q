module
public import OriginalGlobalReconstructionBaseChange318
public section
noncomputable section
namespace OriginalGlobalBaseChangeNaturality318
open AlgebraicGeometry CategoryTheory
open OriginalSchemeDescentData318 OriginalSchemeDescentBaseChangeMaps318
open OriginalGlobalReconstructionBaseChange318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
  [IsAffineHom f] [Flat f] [Surjective f] [IsAffineHom g] [Flat g] [Surjective g]
  (a : X' ⟶ X) (b : Y' ⟶ Y) (square : a ≫ f = g ≫ b)

/-- Every original compatible covering map commutes with the exact
changing-base reconstruction comparison on the whole base scheme. -/
lemma comparison_natural {D E : Datum f} (h : Hom D E) :
    (Scheme.Modules.pullback b).map (AffineGlobalMorphismEffectivity318.map f h) ≫
      (comparison f g a b square E).hom =
    (comparison f g a b square D).hom ≫
      AffineGlobalMorphismEffectivity318.map g (OriginalSchemeDescentBaseChangeMaps318.map g a b square h) := by
  let m := AffineGlobalMorphismEffectivity318.map f h
  let P := Scheme.Modules.pullback g
  have hn := (ActualDescentBaseChangeDiagram318.coverComparison f g a b square).inv.naturality m
  change P.map ((Scheme.Modules.pullback b).map m) ≫ (coverPath f g a b square E).inv =
    (coverPath f g a b square D).inv ≫
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback f).map m) at hn
  apply GlobalAffineLineFaithfulness318.pullback_injective g
  apply (cancel_mono (changedComparison f g a b square E).hom).mp
  simp only [Functor.map_comp,Category.assoc]
  rw [comparison_cover,AffineGlobalMapCoverSquare318.cover_square]
  rw [← Category.assoc (P.map (comparison f g a b square D).hom),comparison_cover]
  rw [← Category.assoc (P.map ((Scheme.Modules.pullback b).map m)),hn,Category.assoc,
    ← Functor.map_comp,AffineGlobalMapCoverSquare318.cover_square,Functor.map_comp,Category.assoc]
end OriginalGlobalBaseChangeNaturality318
