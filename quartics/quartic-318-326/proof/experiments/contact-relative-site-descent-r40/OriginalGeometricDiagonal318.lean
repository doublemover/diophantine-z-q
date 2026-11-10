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

set_option profiler true in
set_option profiler.threshold 0 in
/-- Opaque categorical composition/identity bridge. The concrete input
and output arrows are named before specializing any sheaf carrier. -/
private lemma split_named {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E : C} {X Y Z : D}
    (a : X ⟶ Y) (b : Y ⟶ F.obj A) (d : A ⟶ B) (e : B ⟶ E)
    (c : X ⟶ Z) (t : Z ⟶ F.obj B) (r : Z ⟶ F.obj E)
    (hc : a ≫ b ≫ F.map d=c ≫ t) (hi : t ≫ F.map e=r)
    (left right : X ⟶ F.obj E)
    (hl : left=(a ≫ b) ≫ F.map (d ≫ e)) (hr : right=c ≫ r) : left=right := by
  rw [hl,hr,F.map_comp]
  calc
    (a ≫ b) ≫ (F.map d ≫ F.map e)=(a ≫ b ≫ F.map d) ≫ F.map e := by
      simp only [Category.assoc]
    _ = (c ≫ t) ≫ F.map e := congrArg (fun q => q ≫ F.map e) hc
    _ = c ≫ r := by rw [Category.assoc,hi]

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_named"
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
/-- Projection identity checked at abstract categories and objects. No
concrete scheme/module carrier is unfolded inside this proof term. -/
private lemma mapped_iso_formula {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ D) {X Y : E} {A B Z : C}
    (s : X ≅ Y) (t : G.obj Y ≅ F.obj A) (d : A ≅ B) (e : B ≅ Z) :
    (G.mapIso s ≪≫ t).hom ≫ F.map (d ≪≫ e).hom=
      (G.map s.hom ≫ t.hom) ≫ F.map (d.hom ≫ e.hom) := rfl

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after mapped_iso_formula"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_mapIso_projection {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (L : Line (Spec S)) :
    ((ModuleCat.extendScalars g.hom).mapIso (sectionsIso f L)).hom=
      (ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom :=
  Functor.mapIso_hom _ _

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_mapIso_projection"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_trans_projection {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (L : Line (Spec S)) :
    ((ModuleCat.extendScalars g.hom).mapIso (sectionsIso f L) ≪≫
      sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom=
      ((ModuleCat.extendScalars g.hom).mapIso (sectionsIso f L)).hom ≫
        (sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom :=
  Iso.trans_hom _ _

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_trans_projection"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_sections_projection {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (L : Line (Spec S)) :
    ((ModuleCat.extendScalars g.hom).mapIso (sectionsIso f L) ≪≫
      sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom=
      (ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom ≫
        (sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom := by
  rw [split_trans_projection,split_mapIso_projection]

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_sections_projection"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_path_projection {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) :
    ((pullbackAlong f g (𝟙 S) hh).app L.object).hom=
      (pullbackAlong f g (𝟙 S) hh).hom.app L.object :=
  Iso.app_hom _ _

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_path_projection"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_identity_projection (S : CommRingCat.{u}) (L : Line (Spec S)) :
    ((TildePullbackIdentity318.pullbackId S).app L.object).hom=
      (TildePullbackIdentity318.pullbackId S).hom.app L.object :=
  Iso.app_hom _ _

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_identity_projection"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_sheaf_projection {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) :
    (splitSheaf f g hh L).hom=
      ((pullbackAlong f g (𝟙 S) hh).app L.object).hom ≫
        ((TildePullbackIdentity318.pullbackId S).app L.object).hom :=
  Iso.trans_hom _ _

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_sheaf_projection"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_sheaf_arrow {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) :
    (splitSheaf f g hh L).hom=
      (pullbackAlong f g (𝟙 S) hh).hom.app L.object ≫
        (TildePullbackIdentity318.pullbackId S).hom.app L.object := by
  rw [split_sheaf_projection,split_path_projection,split_identity_projection]

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_sheaf_arrow"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_mapped_generic {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) (G : (Spec S).Modules ⥤ ModuleCat S) :
    G.map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) (splitSheaf f g hh L).hom=
      G.map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) ((pullbackAlong f g (𝟙 S) hh).hom.app L.object ≫
        (TildePullbackIdentity318.pullbackId S).hom.app L.object) :=
  congrArg (fun h : ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object)) ⟶ L.object =>
    G.map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) h)
    (split_sheaf_arrow f g hh L)

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_mapped_generic"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_mapped_explicit {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) :
    (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) (splitSheaf f g hh L).hom=
      (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) ((pullbackAlong f g (𝟙 S) hh).hom.app L.object ≫
        (TildePullbackIdentity318.pullbackId S).hom.app L.object) :=
  split_mapped_generic f g hh L (moduleSpecΓFunctor (R := S))

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_mapped_explicit"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_mapped_projection {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) :
    (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) (splitSheaf f g hh L).hom=
      (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) ((pullbackAlong f g (𝟙 S) hh).hom.app L.object ≫
        (TildePullbackIdentity318.pullbackId S).hom.app L.object) :=
  split_mapped_explicit f g hh L

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_mapped_projection"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_left_formula {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) :
    (((ModuleCat.extendScalars g.hom).mapIso (sectionsIso f L) ≪≫
      sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) (splitSheaf f g hh L).hom)=
    (((ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom) ≫
      (sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom) ≫
      (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) (((pullbackAlong f g (𝟙 S) hh).hom.app L.object) ≫
        ((TildePullbackIdentity318.pullbackId S).hom.app L.object)) := by
  rw [split_sections_projection,split_mapped_projection]

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_left_formula"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_right_formula {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) :
    (ScalarExtensionComposition318.splitIso f.hom g.hom hh
      (OriginalLineAffineModel318.sections S L)).hom=
    (ScalarExtensionComposition318.comparison f.hom g.hom
      (OriginalLineAffineModel318.sections S L) (𝟙 S : S ⟶ S).hom hh).hom ≫
      ((ModuleCat.extendScalarsId S).hom.app (OriginalLineAffineModel318.sections S L)) := by
  exact Iso.trans_hom
    (ScalarExtensionComposition318.comparison f.hom g.hom
      (OriginalLineAffineModel318.sections S L) (RingHom.id S) hh)
    ((ModuleCat.extendScalarsId S).app (OriginalLineAffineModel318.sections S L))

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_right_formula"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma sections_composition_generic {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (h : R ⟶ T)
    (hh : g.hom.comp f.hom=h.hom) (L : Line (Spec R)) :
    (ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom ≫
      (sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      (moduleSpecΓFunctor (R := T)).map
        (X := (Scheme.Modules.pullback (Spec.map g)).obj
          ((Scheme.Modules.pullback (Spec.map f)).obj L.object))
        (Y := (Scheme.Modules.pullback (Spec.map h)).obj L.object)
        ((pullbackAlong f g h hh).hom.app L.object)=
    (ScalarExtensionComposition318.comparison f.hom g.hom
      (OriginalLineAffineModel318.sections R L) h.hom hh).hom ≫
      (sectionsIso h L).hom :=
  OriginalLineNamedComparison318.sections_composition f g h hh L

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after sections_composition_generic"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_composition_explicit {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom=RingHom.id S) (L : Line (Spec S)) :
    (ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom ≫
      (sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := ((Scheme.Modules.pullback (Spec.map (𝟙 S : S ⟶ S))).obj L.object))
        ((pullbackAlong f g (𝟙 S) hh).hom.app L.object)=
    (ScalarExtensionComposition318.comparison f.hom g.hom
      (OriginalLineAffineModel318.sections S L) (𝟙 S : S ⟶ S).hom hh).hom ≫
      (sectionsIso (𝟙 S) L).hom :=
  sections_composition_generic f g (𝟙 S) hh L

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_composition_explicit"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
private lemma split_identity_explicit (S : CommRingCat.{u}) (L : Line (Spec S)) :
    (sectionsIso (𝟙 S) L).hom ≫
      (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map (𝟙 S : S ⟶ S))).obj L.object)) (Y := L.object)
        ((TildePullbackIdentity318.pullbackId S).hom.app L.object)=
    (ModuleCat.extendScalarsId S).hom.app (OriginalLineAffineModel318.sections S L) :=
by
  letI : Mono (Scheme.Modules.fromTildeΓNatTrans.app L.object) := by
    change Mono L.object.fromTildeΓ
    rw [← OriginalLineAffineModel318.canonicalIso_hom S L]
    infer_instance
  exact OriginalLineComparisonIdentity318.counit_comparison_identity
    (tilde.functor S) (moduleSpecΓFunctor (R := S))
    Scheme.Modules.fromTildeΓNatTrans (extendedSections (𝟙 S) L)
    L.object ((Scheme.Modules.pullback (Spec.map (𝟙 S : S ⟶ S))).obj L.object)
    (sectionsIso (𝟙 S) L).hom ((TildePullbackIdentity318.pullbackId S).hom.app L.object)
    ((ModuleCat.extendScalarsId S).hom.app (OriginalLineAffineModel318.sections S L))
    (sheafIso (𝟙 S) L).hom
    (OriginalLineComparisonComposition318.sectionsIso_counit (𝟙 S) L)
    (OriginalLineComparisonIdentity318.sheaf_identity S L)

run_cmd do
  let e ← IO.getStderr
  e.putStrLn "DIAGONAL after split_identity_explicit"
  e.flush

set_option profiler true in
set_option profiler.threshold 0 in
lemma split_sections {S D : CommRingCat.{u}} (f : S ⟶ D) (g : D ⟶ S)
    (hh : g.hom.comp f.hom = RingHom.id S) (L : Line (Spec S)) :
    ((ModuleCat.extendScalars g.hom).mapIso (sectionsIso f L) ≪≫
      sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) (splitSheaf f g hh L).hom =
    (ScalarExtensionComposition318.splitIso f.hom g.hom hh
      (OriginalLineAffineModel318.sections S L)).hom := by
  exact split_named (moduleSpecΓFunctor (R := S))
    (A := ((Scheme.Modules.pullback (Spec.map g)).obj ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (B := ((Scheme.Modules.pullback (Spec.map (𝟙 S : S ⟶ S))).obj L.object)) (E := L.object)
    (X := (ModuleCat.extendScalars g.hom).obj (extendedSections f L))
    (Y := (ModuleCat.extendScalars g.hom).obj
      (OriginalLineAffineModel318.sections D (LineSheafPullback318.line (Spec.map f) L)))
    (Z := extendedSections (𝟙 S) L)
    ((ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom)
    (sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom
    ((pullbackAlong f g (𝟙 S) hh).hom.app L.object)
    ((TildePullbackIdentity318.pullbackId S).hom.app L.object)
    (ScalarExtensionComposition318.comparison f.hom g.hom
      (OriginalLineAffineModel318.sections S L) (𝟙 S : S ⟶ S).hom hh).hom
    (sectionsIso (𝟙 S) L).hom
    ((ModuleCat.extendScalarsId S).hom.app (OriginalLineAffineModel318.sections S L))
    (split_composition_explicit f g hh L)
    (split_identity_explicit S L)
    (((ModuleCat.extendScalars g.hom).mapIso (sectionsIso f L) ≪≫
      sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      (moduleSpecΓFunctor (R := S)).map (X := ((Scheme.Modules.pullback (Spec.map g)).obj
        ((Scheme.Modules.pullback (Spec.map f)).obj L.object))) (Y := L.object) (splitSheaf f g hh L).hom)
    (ScalarExtensionComposition318.splitIso f.hom g.hom hh
      (OriginalLineAffineModel318.sections S L)).hom
    (split_left_formula f g hh L)
    (split_right_formula f g hh L)

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
