module
public import Mathlib.Algebra.Category.Grp.Biproducts
public section
noncomputable section
namespace AbelianProductCoordinates318
open CategoryTheory CategoryTheory.Limits
universe u
variable {I : Type u} (A : I → Ab.{u})
/-- The actual categorical product identified with the literal dependent
function group using its universal property. -/
@[expose] def piIso : ∏ᶜ A ≅ AddCommGrpCat.of (∀ i, A i) :=
  (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone A).isLimit
lemma hom_projection (i : I) :
    (piIso A).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun i => A i) i) = Pi.π A i :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)
lemma hom_apply (x : ∏ᶜ A) (i : I) : (piIso A).hom x i = Pi.π A i x :=
  congrArg (fun f : (∏ᶜ A) ⟶ A i => f x) (hom_projection A i)
end AbelianProductCoordinates318
