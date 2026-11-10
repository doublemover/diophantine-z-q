module
public import OriginalSchemeDescentBaseChangeMaps318
public section
noncomputable section
namespace AffineChangedBaseEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S R' S' : CommRingCat.{u}) [Algebra R S] [Algebra R' S']
  (a : Spec S' ⟶ Spec S) (b : Spec R' ⟶ Spec R)
  (square : a ≫ ActualAffineDoubleNerve318.baseMap R S = ActualAffineDoubleNerve318.baseMap R' S' ≫ b)

/-- Changing affine base retains the original pulled-back line and actual
categorical overlap. New diagonal/triple laws are derived from the old ones. -/
@[expose] def datum (D : ActualAffineDescentData318.Datum R S) :
    ActualAffineDescentData318.Datum R' S' :=
  OriginalSchemeDescentData318.toAffine R' S'
    (OriginalSchemeDescentBaseChange318.datum (ActualAffineDoubleNerve318.baseMap R S)
      (ActualAffineDoubleNerve318.baseMap R' S') a b square (OriginalSchemeDescentData318.ofAffine R S D))

@[expose] def map {D E : ActualAffineDescentData318.Datum R S} (h : ActualAffineDescentData318.Hom D E) :
    ActualAffineDescentData318.Hom (datum R S R' S' a b square D) (datum R S R' S' a b square E) where
  sheafHom := (Scheme.Modules.pullback a).map h.sheafHom
  commutes := (OriginalSchemeDescentBaseChangeMaps318.map
    (ActualAffineDoubleNerve318.baseMap R' S') a b square
    (show OriginalSchemeDescentBaseChangeMaps318.Hom
      (OriginalSchemeDescentData318.ofAffine R S D) (OriginalSchemeDescentData318.ofAffine R S E) from
        { sheafHom := h.sheafHom, commutes := h.commutes })).commutes

variable [Module.FaithfullyFlat R' S']

/-- The changed affine datum is effective using the actual original
reconstruction; no new diagonal, triple or scalar compatibility is supplied. -/
abbrev line (D : ActualAffineDescentData318.Datum R S) :=
  ActualAffineDescendedMaps318.line (datum R S R' S' a b square D)
abbrev comparison (D : ActualAffineDescentData318.Datum R S) :=
  ActualAffineDescendedMaps318.comparison (datum R S R' S' a b square D)

lemma comparison_commutes (D : ActualAffineDescentData318.Datum R S) :
    CanonicalSheafOverlap318.actual (line R S R' S' a b square D).object
        (ActualAffineDoubleNerve318.baseMap R' S') ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (ActualAffineDoubleNerve318.baseMap R' S'))).map
        (comparison R S R' S' a b square D).hom =
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (ActualAffineDoubleNerve318.baseMap R' S'))).map
        (comparison R S R' S' a b square D).hom ≫ (datum R S R' S' a b square D).overlap :=
  ActualAffineEffectiveComparison318.comparison_commutes R' S'
    (datum R S R' S' a b square D).line (datum R S R' S' a b square D).overlap
    (datum R S R' S' a b square D).diagonal (datum R S R' S' a b square D).triple

/-- The same original covering map after pullback a has a unique descended
map on the changed affine base, with the unchanged reconstruction comparisons. -/
theorem maps_effective {D E : ActualAffineDescentData318.Datum R S}
    (h : ActualAffineDescentData318.Hom D E) :
    ∃! k : (line R S R' S' a b square D).object ⟶ (line R S R' S' a b square E).object,
      (Scheme.Modules.pullback (ActualAffineDoubleNerve318.baseMap R' S')).map k ≫
          (comparison R S R' S' a b square E).hom =
        (comparison R S R' S' a b square D).hom ≫ (Scheme.Modules.pullback a).map h.sheafHom :=
  ActualAffineDescendedMaps318.exists_unique_map (map R S R' S' a b square h)
end AffineChangedBaseEffectivity318
