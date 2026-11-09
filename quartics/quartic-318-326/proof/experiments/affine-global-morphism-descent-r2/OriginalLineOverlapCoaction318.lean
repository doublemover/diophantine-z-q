module
public import AffineOverlapCoaction318
public import OriginalLineAffineBaseChange318
public section
noncomputable section
namespace OriginalLineOverlapCoaction318
open CategoryTheory AlgebraicGeometry LineSheafClass318 AffineModuleBaseChange318
set_option maxHeartbeats 700000
set_option profiler true
set_option profiler.threshold 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (L : Line (Spec S))
abbrev sections := OriginalLineAffineModel318.sections S L
abbrev first := (LineSheafPullback318.line (Spec.map (leftMap R S S)) L).object
abbrev second := (LineSheafPullback318.line (Spec.map (rightMap R S S)) L).object

/-- Every actual module-sheaf morphism on the original double overlap
corresponds to exactly one morphism of the original scalar-extended
section modules. The isomorphisms are the canonical tilde pullback and
section comparisons, not substitute line objects. -/
@[expose] def moduleHomEquiv : (first R S L ⟶ second R S L) ≃
    (AffineOverlapCoaction318.first R S (sections S L) ⟶
      AffineOverlapCoaction318.second R S (sections S L)) :=
  ((OriginalLineAffineBaseChange318.sheafIso (leftMap R S S) L).symm.homCongr
      (Iso.refl (second R S L))).trans <|
    ((tilde.adjunction (R := ring R S S)).homEquiv _ _).trans <|
      (Iso.refl _).homCongr
        (OriginalLineAffineBaseChange318.sectionsIso (rightMap R S S) L).symm

/-- The equivalence is exactly original global sections of the given
morphism, conjugated by the two canonical section comparisons. -/
lemma moduleHomEquiv_apply (h : first R S L ⟶ second R S L) :
    moduleHomEquiv R S L h =
      (OriginalLineAffineBaseChange318.sectionsIso (leftMap R S S) L).hom ≫
        moduleSpecΓFunctor.map h ≫
          (OriginalLineAffineBaseChange318.sectionsIso (rightMap R S S) L).inv := by
  simp only [moduleHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.symm_inv, Iso.refl_hom, Category.comp_id, Iso.refl_inv, Category.id_comp,
    Iso.symm_hom, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rfl

/-- Exact conversion of an original geometric overlap morphism into a
candidate map for the original scalar-extension comonad. This equivalence
retains all overlap maps and does not assert its coalgebra laws. -/
@[expose] def homEquiv : (first R S L ⟶ second R S L) ≃
    (sections S L ⟶ AffineOverlapCoaction318.comonadObject R S (sections S L)) :=
  (moduleHomEquiv R S L).trans (AffineOverlapCoaction318.homEquiv R S (sections S L))

lemma homEquiv_injective : Function.Injective (homEquiv R S L) :=
  (homEquiv R S L).injective

lemma homEquiv_surjective : Function.Surjective (homEquiv R S L) :=
  (homEquiv R S L).surjective

/-- Every candidate map has one and only one actual original overlap
sheaf morphism. Diagonal and triple-overlap equations are a further step. -/
lemma unique_overlap (a : sections S L ⟶
    AffineOverlapCoaction318.comonadObject R S (sections S L)) :
    ∃! h : first R S L ⟶ second R S L, homEquiv R S L h = a := by
  exact ⟨(homEquiv R S L).symm a, (homEquiv R S L).apply_symm_apply a,
    fun h hh => (homEquiv R S L).injective (hh.trans ((homEquiv R S L).apply_symm_apply a).symm)⟩
end OriginalLineOverlapCoaction318
