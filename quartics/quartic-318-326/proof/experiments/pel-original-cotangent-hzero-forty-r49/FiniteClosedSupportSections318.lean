module
public import FiniteClosedSupportSheaf318
public section
noncomputable section
namespace FiniteClosedSupportSections318
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
universe u
attribute [local instance] Classical.propDecidable
variable {X : TopCat.{u}} (F : Sheaf Ab X) {I : Type u} [Finite I] (p : I → X)
/-- Actual evaluation at the whole open set, not an exactness assertion. -/
abbrev sections : Sheaf Ab X ⥤ Ab :=
  Sheaf.forget Ab X ⋙ (evaluation (Opens X)ᵒᵖ Ab).obj (op ⊤)
/-- The whole open contains the support point, so the skyscraper's
actual global sections are canonically its defining stalk. -/
@[expose] def pieceSections (i : I) :
    (sections (X := X)).obj (FiniteClosedSupportSheaf318.pieces F p i) ≅ F.obj.stalk (p i) :=
  eqToIso (by simp [sections,FiniteClosedSupportSheaf318.pieces,
    skyscraperSheaf,skyscraperPresheaf])
lemma unit_sections (i : I) :
    (sections (X := X)).map ((stalkSkyscraperSheafAdjunction (p i)).unit.app F) ≫
      (pieceSections F p i).hom = F.obj.germ ⊤ (p i) trivial := by
  simp [sections,pieceSections,stalkSkyscraperSheafAdjunction,
    StalkSkyscraperPresheafAdjunctionAuxs.unit,
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf]
/-- The literal global-germ morphism, with a categorical product target. -/
@[expose] def globalGerms : F.obj.obj (op ⊤) ⟶ ∏ᶜ fun i => F.obj.stalk (p i) :=
  Pi.lift (fun i => F.obj.germ ⊤ (p i) trivial)
lemma globalGerms_factorization : globalGerms F p =
    (sections (X := X)).map (FiniteClosedSupportSheaf318.toPieces F p) ≫
      piComparison (sections (X := X)) (FiniteClosedSupportSheaf318.pieces F p) ≫
      (Pi.mapIso (pieceSections F p)).hom := by
  apply Pi.hom_ext
  intro i
  rw [globalGerms,Pi.lift_π]
  simp only [Category.assoc,Pi.mapIso_hom_π,piComparison_comp_π_assoc,
    ←Functor.map_comp_assoc]
  rw [FiniteClosedSupportSheaf318.toPieces,Pi.lift_π]
  exact (unit_sections F p i).symm
/-- Global sections really are the product of the actual support stalks.
This follows by evaluating an already-proved sheaf ISOMORPHISM; it does
not infer global-section surjectivity from stalkwise surjectivity. -/
theorem globalGerms_isIso (hinj : Function.Injective p)
    (hp : ∀ i, IsClosed ({p i} : Set X))
    (hz : ∀ x, x ∉ Set.range p → IsZero (F.obj.stalk x)) : IsIso (globalGerms F p) := by
  haveI := FiniteClosedSupportSheaf318.toPieces_isIso F p hinj hp hz
  rw [globalGerms_factorization]
  infer_instance
end FiniteClosedSupportSections318
