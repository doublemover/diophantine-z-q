module
public import OriginalAffineMorphismDescent318
public section
noncomputable section
namespace OriginalAffineReconstructionUnit318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualAffineDescentData318 ActualAffineDoubleNerve318 CanonicalActualDescentFunctor318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]

/-- The inverse of an actual compatible covering isomorphism is compatible
with the same original canonical overlaps; no second square is assumed. -/
lemma inverse_compatible {L K : Line (Spec R)}
    (a : (Scheme.Modules.pullback (baseMap R S)).obj L.object ≅
      (Scheme.Modules.pullback (baseMap R S)).obj K.object)
    (h : (datum R S L).overlap ≫
        (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map a.hom =
      (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map a.hom ≫
        (datum R S K).overlap) :
    (datum R S K).overlap ≫
        (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map a.inv =
      (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map a.inv ≫
        (datum R S L).overlap := by
  let p := (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).mapIso a
  let q := (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).mapIso a
  change (datum R S L).overlap ≫ q.hom = p.hom ≫ (datum R S K).overlap at h
  change (datum R S K).overlap ≫ q.inv = p.inv ≫ (datum R S L).overlap
  apply (cancel_epi p.hom).mp
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

abbrev reconstructed (L : Line (Spec R)) := ActualAffineDescendedMaps318.line (datum R S L)
abbrev coverComparison (L : Line (Spec R)) := ActualAffineDescendedMaps318.comparison (datum R S L)

/-- The exact reconstruction comparison is an original canonical descent
morphism from the reconstructed line back to the given original line. -/
@[expose] def forward (L : Line (Spec R)) :
    Hom (datum R S (reconstructed R S L)) (datum R S L) where
  sheafHom := (coverComparison R S L).hom
  commutes := ActualAffineEffectiveComparison318.comparison_commutes R S
    (datum R S L).line (datum R S L).overlap (datum R S L).diagonal (datum R S L).triple

@[expose] def backward (L : Line (Spec R)) :
    Hom (datum R S L) (datum R S (reconstructed R S L)) where
  sheafHom := (coverComparison R S L).inv
  commutes := inverse_compatible R S (coverComparison R S L) (forward R S L).commutes

/-- Reconstructing the canonical descent datum returns the actual original
line up to a specified sheaf isomorphism, whose pullback is the original
reconstruction comparison. This is the missing object-identity join. -/
@[expose] def unitIso (L : Line (Spec R)) : (reconstructed R S L).object ≅ L.object :=
  OriginalAffineMorphismDescent318.descendedIso R S (forward R S L) (backward R S L)
    (coverComparison R S L).hom_inv_id (coverComparison R S L).inv_hom_id

lemma unitIso_cover (L : Line (Spec R)) :
    (Scheme.Modules.pullback (baseMap R S)).map (unitIso R S L).hom =
      (coverComparison R S L).hom :=
  OriginalAffineMorphismDescent318.descend_cover R S (forward R S L)

/-- The recovered original-object isomorphism is natural for every original
base-line morphism, with exact actual reconstruction maps. -/
lemma unitIso_natural {L K : Line (Spec R)} (g : L.object ⟶ K.object) :
    ActualAffineDescendedMaps318.map (map R S g) ≫ (unitIso R S K).hom =
      (unitIso R S L).hom ≫ g := by
  apply OriginalAffineLineFaithfulness318.pullback_map_injective R S
  rw [Functor.map_comp, Functor.map_comp, unitIso_cover, unitIso_cover]
  exact ActualAffineDescendedMaps318.map_commutes (map R S g)
end OriginalAffineReconstructionUnit318
