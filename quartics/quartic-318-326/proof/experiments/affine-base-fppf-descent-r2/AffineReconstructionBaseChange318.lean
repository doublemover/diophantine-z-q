module
public import CanonicalDescentBaseChange318
public section
noncomputable section
namespace AffineReconstructionBaseChange318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualAffineDescentData318 ActualAffineDoubleNerve318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Inverse compatibility for actual arbitrary affine descent overlaps is
a consequence of the original square and the original covering iso. -/
@[expose] def inverseHom {R S : CommRingCat.{u}} [Algebra R S] {D E : Datum R S}
    (e : D.line.object ≅ E.line.object)
    (h : D.overlap ≫ (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map e.hom =
      (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map e.hom ≫ E.overlap) : Hom E D where
  sheafHom := e.inv
  commutes := by
    let p := (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).mapIso e
    let q := (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).mapIso e
    change D.overlap ≫ q.hom = p.hom ≫ E.overlap at h
    change E.overlap ≫ q.inv = p.inv ≫ D.overlap
    apply (cancel_epi p.hom).mp
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

variable (R S R' S' : CommRingCat.{u}) [Algebra R S] [Algebra R' S']
  [Module.FaithfullyFlat R S] [Module.FaithfullyFlat R' S']
  (a : Spec S' ⟶ Spec S) (b : Spec R' ⟶ Spec R)
  (square : a ≫ baseMap R S = baseMap R' S' ≫ b) (D : Datum R S)

abbrev changed := AffineChangedBaseEffectivity318.datum R S R' S' a b square D
variable {R S} in
abbrev originalLine := ActualAffineDescendedMaps318.line D
variable {R S R'} in
abbrev pulledLine := LineSheafPullback318.line b (originalLine D)
abbrev changedLine := ActualAffineDescendedMaps318.line (changed R S R' S' a b square D)

@[expose] def originalComparisonHom :
    Hom (CanonicalActualDescentFunctor318.datum R S (originalLine D)) D where
  sheafHom := (ActualAffineDescendedMaps318.comparison D).hom
  commutes := ActualAffineEffectiveComparison318.comparison_commutes R S
    D.line D.overlap D.diagonal D.triple

abbrev coverPath := (ActualDescentBaseChangeDiagram318.coverComparison
  (baseMap R S) (baseMap R' S') a b square).app (originalLine D).object

/-- The canonical square comparison is an actual descent morphism. Its
compatibility is the proved canonical-overlap base-change theorem. -/
@[expose] def canonicalInverse :
    Hom (CanonicalActualDescentFunctor318.datum R' S' (pulledLine b D))
      (AffineChangedBaseEffectivity318.datum R S R' S' a b square
        (CanonicalActualDescentFunctor318.datum R S (originalLine D))) :=
  inverseHom (coverPath R S R' S' a b square D)
    (CanonicalDescentBaseChange318.overlap_square (baseMap R S) (baseMap R' S') a b square
      (originalLine D).object)

/-- The old reconstruction comparison after actual pullback a, normalized
by the exact original square path, supplies the changed datum comparison. -/
@[expose] def toChanged :
    Hom (CanonicalActualDescentFunctor318.datum R' S' (pulledLine b D))
      (changed R S R' S' a b square D) :=
  (canonicalInverse R S R' S' a b square D).comp
    (AffineChangedBaseEffectivity318.map R S R' S' a b square (originalComparisonHom R S D))

abbrev changedComparison := ActualAffineDescendedMaps318.comparison (changed R S R' S' a b square D)

@[expose] def changedComparisonHom :
    Hom (CanonicalActualDescentFunctor318.datum R' S' (changedLine R S R' S' a b square D))
      (changed R S R' S' a b square D) where
  sheafHom := (changedComparison R S R' S' a b square D).hom
  commutes := ActualAffineEffectiveComparison318.comparison_commutes R' S'
    (changed R S R' S' a b square D).line (changed R S R' S' a b square D).overlap
    (changed R S R' S' a b square D).diagonal (changed R S R' S' a b square D).triple

/-- The exact covering iso comparing the two original candidate base lines. -/
@[expose] def coveringIso :
    (Scheme.Modules.pullback (baseMap R' S')).obj (pulledLine b D).object ≅
      (Scheme.Modules.pullback (baseMap R' S')).obj (changedLine R S R' S' a b square D).object :=
  (coverPath R S R' S' a b square D).symm ≪≫
    (Scheme.Modules.pullback a).mapIso (ActualAffineDescendedMaps318.comparison D) ≪≫
      (changedComparison R S R' S' a b square D).symm

@[expose] def coveringHom :
    Hom (CanonicalActualDescentFunctor318.datum R' S' (pulledLine b D))
      (CanonicalActualDescentFunctor318.datum R' S' (changedLine R S R' S' a b square D)) :=
  (toChanged R S R' S' a b square D).comp
    (inverseHom (changedComparison R S R' S' a b square D)
      (changedComparisonHom R S R' S' a b square D).commutes)

/-- The reconstruction on the changed affine base is isomorphic to the
literal b-pullback of the old original reconstructed line. The iso is
constructed by original geometric morphism descent, not postulated. -/
@[expose] def comparison : (pulledLine b D).object ≅ (changedLine R S R' S' a b square D).object :=
  OriginalAffineMorphismDescent318.descendedIso R' S'
    (coveringHom R S R' S' a b square D)
    (inverseHom (coveringIso R S R' S' a b square D)
      (coveringHom R S R' S' a b square D).commutes)
    (coveringIso R S R' S' a b square D).hom_inv_id
    (coveringIso R S R' S' a b square D).inv_hom_id

/-- The comparison retains the exact actual square and both original
reconstruction maps, which determine it uniquely. -/
lemma comparison_cover :
    (Scheme.Modules.pullback (baseMap R' S')).map (comparison R S R' S' a b square D).hom ≫
        (changedComparison R S R' S' a b square D).hom =
      (coverPath R S R' S' a b square D).inv ≫
        (Scheme.Modules.pullback a).map (ActualAffineDescendedMaps318.comparison D).hom := by
  rw [show (Scheme.Modules.pullback (baseMap R' S')).map (comparison R S R' S' a b square D).hom =
    (coveringIso R S R' S' a b square D).hom from
      OriginalAffineMorphismDescent318.descend_cover R' S' (coveringHom R S R' S' a b square D)]
  simp only [coveringIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma comparison_unique
    (k : (pulledLine b D).object ⟶ (changedLine R S R' S' a b square D).object)
    (hk : (Scheme.Modules.pullback (baseMap R' S')).map k ≫
        (changedComparison R S R' S' a b square D).hom =
      (coverPath R S R' S' a b square D).inv ≫
        (Scheme.Modules.pullback a).map (ActualAffineDescendedMaps318.comparison D).hom) :
    k = (comparison R S R' S' a b square D).hom := by
  apply OriginalAffineLineFaithfulness318.maps_eq_of_cover_square R' S' k
    (comparison R S R' S' a b square D).hom (changedComparison R S R' S' a b square D)
  exact hk.trans (comparison_cover R S R' S' a b square D).symm
end AffineReconstructionBaseChange318
