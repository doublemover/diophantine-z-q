module
public import OriginalGeometricTriple318
public import AffineOverlapDiagonal318
public section
noncomputable section
namespace OriginalGeometricDiagonal318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineAffineBaseChange318
open OriginalLineNamedComparison318 AffineModuleBaseChange318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
set_option stderrAsMessages false

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL imports loaded"
  e.flush

/-- The actual geometric comparison for a split composite ring path. -/
@[expose] def splitSheaf {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom = RingHom.id S) (L : Line (Spec S)) :
    (Scheme.Modules.pullback (Spec.map g)).obj
      ((Scheme.Modules.pullback (Spec.map f)).obj L.object) ≅ L.object :=
  (pullbackAlong f g (𝟙 S) hh).app L.object ≪≫
    (TildePullbackIdentity318.pullbackId S).app L.object

set_option profiler true in
set_option profiler.threshold 0 in
lemma split_sections {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom = RingHom.id S) (L : Line (Spec S)) :
    ((ModuleCat.extendScalars g.hom).mapIso (sectionsIso f L) ≪≫
      sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      moduleSpecΓFunctor.map (splitSheaf f g hh L).hom =
    (ScalarExtensionComposition318.splitIso f.hom g.hom hh
      (OriginalLineAffineModel318.sections S L)).hom := by
  have h := congrArg
    (fun k => k ≫ moduleSpecΓFunctor.map
      ((TildePullbackIdentity318.pullbackId S).hom.app L.object))
    (sections_composition f g (𝟙 S) hh L)
  simpa only [splitSheaf, ScalarExtensionComposition318.splitIso, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    OriginalLineComparisonIdentity318.sections_identity,
    Functor.id_obj,CommRingCat.hom_id,Iso.app_hom] using h

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_sections"
  e.flush

variable (R S : CommRingCat.{u}) [Algebra R S] (L : Line (Spec S))
  (τ : OriginalLineOverlapCoaction318.first R S L ⟶
    OriginalLineOverlapCoaction318.second R S L)
abbrev diagonal := AffineOverlapDiagonal318.diagonal R S
abbrev firstComparison := splitSheaf (leftMap R S S) (diagonal R S)
  (AffineOverlapDiagonal318.diagonal_left R S) L
abbrev secondComparison := splitSheaf (rightMap R S S) (diagonal R S)
  (AffineOverlapDiagonal318.diagonal_right R S) L

/-- The genuine geometric identity on the diagonal, with both original
canonical split-pullback comparisons to the unchanged line L. -/
@[expose] def Diagonal : Prop :=
  (Scheme.Modules.pullback (Spec.map (diagonal R S))).map τ ≫
    (secondComparison R S L).hom = (firstComparison R S L).hom

set_option profiler true in
set_option profiler.threshold 0 in
lemma diagonal_to_split (hτ : Diagonal R S L τ) :
    (ModuleCat.extendScalars (diagonal R S).hom).map
      (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ) ≫
      (ScalarExtensionComposition318.splitIso (rightMap R S S).hom (diagonal R S).hom
        (AffineOverlapDiagonal318.diagonal_right R S)
        (OriginalLineAffineModel318.sections S L)).hom =
    (ScalarExtensionComposition318.splitIso (leftMap R S S).hom (diagonal R S).hom
      (AffineOverlapDiagonal318.diagonal_left R S)
      (OriginalLineAffineModel318.sections S L)).hom := by
  let a := (ModuleCat.extendScalars (diagonal R S).hom).mapIso (sectionsIso (leftMap R S S) L) ≪≫
    sectionsIso (diagonal R S) (LineSheafPullback318.line (Spec.map (leftMap R S S)) L)
  let b := (ModuleCat.extendScalars (diagonal R S).hom).mapIso (sectionsIso (rightMap R S S) L) ≪≫
    sectionsIso (diagonal R S) (LineSheafPullback318.line (Spec.map (rightMap R S S)) L)
  have hp := AffineSectionConjugation318.pulled_morphism L
    (leftMap R S S) (rightMap R S S) (diagonal R S) τ
  rw [OriginalGeometricTriple318.overlap_map, ← hp,
    ← split_sections (rightMap R S S) (diagonal R S)
      (AffineOverlapDiagonal318.diagonal_right R S) L]
  change (a.hom ≫ moduleSpecΓFunctor.map
    ((Scheme.Modules.pullback (Spec.map (diagonal R S))).map τ) ≫ b.inv) ≫
    (b.hom ≫ moduleSpecΓFunctor.map (secondComparison R S L).hom) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp, hτ]
  exact split_sections (leftMap R S S) (diagonal R S)
    (AffineOverlapDiagonal318.diagonal_left R S) L
run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after diagonal_to_split"
  e.flush

end OriginalGeometricDiagonal318
