module
public import OriginalGlobalBaseChangeNaturality318
public section
noncomputable section
namespace OriginalGlobalBaseChangeFunctor318
open AlgebraicGeometry CategoryTheory
open OriginalGlobalDescentCategory318 OriginalGlobalSquareFunctor318
open scoped OriginalGlobalDescentCategory318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y')
  [IsAffineHom f] [Flat f] [Surjective f] [IsAffineHom g] [Flat g] [Surjective g]
  (a : X' ⟶ X) (b : Y' ⟶ Y) (square : a ≫ f = g ≫ b)

/-- A natural isomorphism on the unchanged whole-scheme descent
categories, using the actual original sheaf pullback on the base. -/
@[expose] def comparison : reconstruct f ⋙ linePullback b ≅
    change f g a b square ⋙ reconstruct g :=
  NatIso.ofComponents (fun D =>
    { hom := (OriginalGlobalReconstructionBaseChange318.comparison f g a b square D).hom
      inv := (OriginalGlobalReconstructionBaseChange318.comparison f g a b square D).inv
      hom_inv_id := (OriginalGlobalReconstructionBaseChange318.comparison f g a b square D).hom_inv_id
      inv_hom_id := (OriginalGlobalReconstructionBaseChange318.comparison f g a b square D).inv_hom_id }) (by
    intro D E h
    exact OriginalGlobalBaseChangeNaturality318.comparison_natural f g a b square h)

/-- The displayed component is characterized by the original covering
square, not by an arbitrary choice of categorical isomorphism. -/
lemma component_cover (D : OriginalSchemeDescentData318.Datum f) :
    (Scheme.Modules.pullback g).map ((comparison f g a b square).hom.app D) ≫
      (OriginalGlobalReconstructionBaseChange318.changedComparison f g a b square D).hom =
    (OriginalGlobalReconstructionBaseChange318.coverPath f g a b square D).inv ≫
      (Scheme.Modules.pullback a).map (AffineMorphismGlobalRecovery318.comparison f D).hom :=
  OriginalGlobalReconstructionBaseChange318.comparison_cover f g a b square D
end OriginalGlobalBaseChangeFunctor318
