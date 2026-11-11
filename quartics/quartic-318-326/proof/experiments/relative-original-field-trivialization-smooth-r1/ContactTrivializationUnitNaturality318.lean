module
public import ContactTrivializationFullNaturality318
public import ContactTrivializationPointUnits318
public import OriginalFrameTransportUnits318
public section
noncomputable section
namespace ContactTrivializationUnitNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactTrivializationAffinePoints318
variable (R S T : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S] [Algebra ℚ T]
  (f : R →ₐ[ℚ] S) (g : S →ₐ[ℚ] T) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Algebra R T := (g.comp f).toAlgebra
local notation "U" => ContactArbitraryNowhereZeroOpen318.locus R c L
local notation "φ" => ContactHZeroCoefficientFunctor318.coefficientArrow R S f T g
local notation "p" => ContactRelativeCoefficientChange318.curveMap S T g c
local notation "mapPoint" => AffineOpenPointNaturality318.map R
  (ContactArbitrarySectionParameter318.parameterRing R c L) S T U φ

/-- The actual represented trivialization points carry a NATURAL unit
action for arbitrary coefficient change. The units are pulled along the
actual original curve map, without identifying them with base units. -/
lemma action (u : Γ(curve S c,⊤)ˣ) (x : Points R c L S f) :
    mapPoint (ContactTrivializationPointUnits318.act R c L S f u x)=
      ContactTrivializationPointUnits318.act R c L T (g.comp f)
        (OriginalFramePullbackUnits318.units p u) (mapPoint x) := by
  apply (equivalence R c L T (g.comp f)).injective
  rw [ContactTrivializationPointUnits318.frame_act]
  have h := ContactTrivializationFullNaturality318.natural R S T f g c L
    (ContactTrivializationPointUnits318.act R c L S f u x)
  rw [ContactTrivializationPointUnits318.frame_act,OriginalFramePullbackUnits318.action,
    OriginalFrameTransportUnits318.action,
    ContactTrivializationFullNaturality318.natural] at h
  exact h.symm

lemma ratio (x y : Points R c L S f) :
    ContactTrivializationPointUnits318.ratio R c L T (g.comp f) (mapPoint x) (mapPoint y)=
      OriginalFramePullbackUnits318.units p (ContactTrivializationPointUnits318.ratio R c L S f x y) := by
  unfold ContactTrivializationPointUnits318.ratio
  rw [←ContactTrivializationFullNaturality318.natural R S T f g c L x,
    ←ContactTrivializationFullNaturality318.natural R S T f g c L y,
    OriginalFrameTransportUnits318.ratio,OriginalFramePullbackUnits318.ratio_natural]
end ContactTrivializationUnitNaturality318
