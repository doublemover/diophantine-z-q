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
run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before sections"
  stream.flush

abbrev sections := OriginalLineAffineModel318.sections S L
run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before first"
  stream.flush

abbrev first := (LineSheafPullback318.line (Spec.map (leftMap R S S)) L).object
run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before second"
  stream.flush

abbrev second := (LineSheafPullback318.line (Spec.map (rightMap R S S)) L).object

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before moduleHomEquiv"
  stream.flush

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

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before conjugate_adjunction"
  stream.flush

/-- Categorical calculation before any concrete localization module is
substituted: a conjugated adjunction mate is the unit and mapped arrow. -/
lemma conjugate_adjunction {C : Type*} {E : Type*} [Category C] [Category E]
    {F : C ⥤ E} {G : E ⥤ C} (adj : F ⊣ G) {A B : C} {M N : E}
    (e : F.obj A ≅ M) (d : B ≅ G.obj N) (h : M ⟶ N) :
    ((e.symm.homCongr (Iso.refl N)).trans
      ((adj.homEquiv A N).trans ((Iso.refl A).homCongr d.symm))).toFun h =
    adj.unit.app A ≫ G.map e.hom ≫ G.map h ≫ d.inv := by
  simp only [Equiv.trans_apply,Iso.homCongr_apply,Iso.symm_inv,Iso.refl_hom,
    Category.comp_id,Iso.refl_inv,Category.id_comp,Iso.symm_hom,
    Adjunction.homEquiv_unit,Functor.map_comp,Category.assoc]

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before tilde_unit"
  stream.flush

/-- The old tilde unit is identified at a generic module, avoiding
normalization of a concrete tensor/localization carrier in each consumer. -/
lemma tilde_unit (T : CommRingCat.{u}) (N : ModuleCat.{u} T) :
    (tilde.adjunction (R:=T)).unit.app N = (tilde.isoTop N).hom := rfl

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before moduleHomEquiv_apply"
  stream.flush

/-- The equivalence is exactly original global sections of the given
morphism, conjugated by the two canonical section comparisons. -/
lemma moduleHomEquiv_apply (h : first R S L ⟶ second R S L) :
    (moduleHomEquiv R S L).toFun h =
      (OriginalLineAffineBaseChange318.sectionsIso (leftMap R S S) L).hom ≫
        moduleSpecΓFunctor.map h ≫
          (OriginalLineAffineBaseChange318.sectionsIso (rightMap R S S) L).inv := by
  run_tac do
    let stream ← IO.getStderr
    stream.putStrLn "OVERLAP_MILESTONE moduleHomEquiv_apply generic proof entered"
    stream.flush
  calc
    _ = (tilde.adjunction (R:=ring R S S)).unit.app
          (OriginalLineAffineBaseChange318.extendedSections (leftMap R S S) L) ≫
        moduleSpecΓFunctor.map (OriginalLineAffineBaseChange318.sheafIso (leftMap R S S) L).hom ≫
        moduleSpecΓFunctor.map h ≫
          (OriginalLineAffineBaseChange318.sectionsIso (rightMap R S S) L).inv :=
      conjugate_adjunction (tilde.adjunction (R:=ring R S S))
        (OriginalLineAffineBaseChange318.sheafIso (leftMap R S S) L)
        (OriginalLineAffineBaseChange318.sectionsIso (rightMap R S S) L) h
    _ = _ := by
      rw [tilde_unit,OriginalLineAffineBaseChange318.sectionsIso_hom]
      simp only [Category.assoc]
run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before homEquiv"
  stream.flush

/-- Exact conversion of an original geometric overlap morphism into a
candidate map for the original scalar-extension comonad. This equivalence
retains all overlap maps and does not assert its coalgebra laws. -/
@[expose] def homEquiv : (first R S L ⟶ second R S L) ≃
    (sections S L ⟶ AffineOverlapCoaction318.comonadObject R S (sections S L)) :=
  (moduleHomEquiv R S L).trans (AffineOverlapCoaction318.homEquiv R S (sections S L))

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before homEquiv_injective"
  stream.flush

lemma homEquiv_injective : Function.Injective (homEquiv R S L) :=
  (homEquiv R S L).injective

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before homEquiv_surjective"
  stream.flush

lemma homEquiv_surjective : Function.Surjective (homEquiv R S L) :=
  (homEquiv R S L).surjective

run_cmd do
  let stream ← IO.getStderr
  stream.putStrLn "OVERLAP_MILESTONE before unique_overlap"
  stream.flush

/-- Every candidate map has one and only one actual original overlap
sheaf morphism. Diagonal and triple-overlap equations are a further step. -/
lemma unique_overlap (a : sections S L ⟶
    AffineOverlapCoaction318.comonadObject R S (sections S L)) :
    ∃! h : first R S L ⟶ second R S L, homEquiv R S L h = a := by
  exact ⟨(homEquiv R S L).symm a, (homEquiv R S L).apply_symm_apply a,
    fun h hh => (homEquiv R S L).injective (hh.trans ((homEquiv R S L).apply_symm_apply a).symm)⟩
end OriginalLineOverlapCoaction318
