module
public import RelativeLineBaseChangeIso318
public import RelativeFppfLineSheaf318
public import Mathlib.CategoryTheory.Sites.CoverLifting
public section
noncomputable section
namespace RelativeFppfBaseChangeIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeFppfLineSheaf318
universe u
variable {X S S' : Scheme.{u}} (p : X ⟶ S) (b : S' ⟶ S)

instance map_continuous : (Over.map b).IsContinuous (topology S') (topology S) :=
  inferInstanceAs ((Over.map b).IsContinuous (Scheme.fppfTopology.over S')
    (Scheme.fppfTopology.over S))

instance map_cocontinuous : (Over.map b).IsCocontinuous (topology S') (topology S) :=
  inferInstanceAs ((Over.map b).IsCocontinuous (Scheme.fppfTopology.over S')
    (Scheme.fppfTopology.over S))

/-- Restriction on the actual big fppf over-sites along the actual base map.
The original over-map functor is proved continuous and cocontinuous. -/
@[expose] def restriction :
    Sheaf (topology S) CommGrpCat.{u+1} ⥤ Sheaf (topology S') CommGrpCat.{u+1} :=
  Scheme.fppfTopology.overMapPullback CommGrpCat.{u+1} b

/-- The universal sheafification comparison for the actual over-base
restriction, not a separate base-change compatibility assumption. -/
@[expose] def sheafificationIso :
    (presheafToSheaf (topology S') CommGrpCat.{u+1}).obj
        ((Over.map b).op ⋙ RelativeLineClassBaseChange318.presheaf p) ≅
      (restriction b).obj (sheaf p) :=
  ((Over.map b).pushforwardContinuousSheafificationCompatibility CommGrpCat.{u+1}
    (topology S') (topology S)).app (RelativeLineClassBaseChange318.presheaf p)

/-- The genuine associated fppf sheaf commutes with arbitrary actual base
change: the identification uses both actual fiber-product pullbacks and the
continuous/cocontinuous site comparison. -/
@[expose] def sheafIso :
    (restriction b).obj (sheaf p) ≅ sheaf (pullback.snd p b) :=
  (sheafificationIso p b).symm ≪≫
    (presheafToSheaf (topology S') CommGrpCat.{u+1}).mapIso
      (RelativeLineBaseChangeIso318.presheafIso p b)

/-- The universal comparison preserves the exact original unit maps. -/
lemma sheafification_unit :
    toSheafify (topology S') ((Over.map b).op ⋙ RelativeLineClassBaseChange318.presheaf p) ≫
      (sheafificationIso p b).hom.hom = Functor.whiskerLeft (Over.map b).op (unit p) :=
  (Over.map b).toSheafify_pullbackSheafificationCompatibility CommGrpCat.{u+1}
    (topology S') (topology S) (RelativeLineClassBaseChange318.presheaf p)

/-- The final base-change isomorphism respects the exact original presheaf
comparison and both canonical unit maps. -/
lemma unit_basechange :
    Functor.whiskerLeft (Over.map b).op (unit p) ≫ (sheafIso p b).hom.hom =
      (RelativeLineBaseChangeIso318.presheafIso p b).hom ≫ unit (pullback.snd p b) := by
  let E := (sheafToPresheaf (topology S') CommGrpCat.{u+1}).mapIso
    (sheafificationIso p b)
  let M := (presheafToSheaf (topology S') CommGrpCat.{u+1}).map
    (RelativeLineBaseChangeIso318.presheafIso p b).hom
  calc
    _ = toSheafify (topology S')
        ((Over.map b).op ⋙ RelativeLineClassBaseChange318.presheaf p) ≫ M.hom := by
      rw [← sheafification_unit p b]
      change (_ ≫ E.hom) ≫ (E.inv ≫ M.hom) = _
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := (toSheafify_naturality (topology S')
      (RelativeLineBaseChangeIso318.presheafIso p b).hom).symm
end RelativeFppfBaseChangeIso318
