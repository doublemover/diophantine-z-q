module
public import ContactCartierPresheafEquiv318
public section
noncomputable section
namespace ContactCartierUniversalAbel318
open AlgebraicGeometry CategoryTheory Opposite
variable (c : Fin 4 → ℚˣ) (N : ℕ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- The single actual Abel morphism on the full bounded Cartier moduli
presheaf, valued in the existing original fppf line-class sheaf. -/
@[expose] def transformation : ContactCartierDataPresheaf318.presheaf c N ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1} where
  app T D := ContactBoundedCartierAbelNaturality318.value c N T.unop.hom D
  naturality T U f := by
    funext D
    exact (ContactBoundedCartierAbelNaturality318.natural c N _ _ f.unop.left f.unop.w D).symm
/-- The SAME map on actual bounded parameter points with Cartier fibers. -/
@[expose] def onPoints : ContactCartierPointPresheaf318.presheaf c N ⟶
    (RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1} :=
  (ContactCartierPresheafEquiv318.equivalence c N).inv ≫ transformation c N
lemma classification : (ContactCartierPresheafEquiv318.equivalence c N).hom ≫ onPoints c N=
    transformation c N := by
  simp only [onPoints,←Category.assoc,Iso.hom_inv_id,Category.id_comp]
end ContactCartierUniversalAbel318
