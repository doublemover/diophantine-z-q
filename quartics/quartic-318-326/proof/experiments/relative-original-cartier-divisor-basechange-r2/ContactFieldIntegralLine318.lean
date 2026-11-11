module
public import IntegralLineRestriction318
public import ContactOriginalRelativePolynomialCharts318
public import ContactGeometricallyIntegral318
public section
noncomputable section
namespace ContactFieldIntegralLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : CommRingCat.{0}) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)

/-- Integrality of the SAME original contact curve after an arbitrary
field coefficient extension, obtained from its proved geometric integrality
and its actual original Cartesian family construction. -/
instance integral : IsIntegral (curve K c) := by
  letI : GeometricallyIntegral (ContactOriginalAffineTestCover318.p c) :=
    ContactGeometricallyIntegral318.model_geometricallyIntegral c
  exact GeometricallyIntegral.geometrically_isIntegral
    (f := ContactOriginalAffineTestCover318.p c) (baseMap K)
    (pullback.fst (ContactOriginalAffineTestCover318.p c) (baseMap K))
    (pullback.snd (ContactOriginalAffineTestCover318.p c) (baseMap K)) (.of_hasPullback _ _)

/-- Nonzero genuine original field-fiber sections have regular
coefficients on every actual nonempty original line frame. -/
theorem frame_regular (L : Line (curve K c)) (s : Γ(L.object,⊤)) (hs : s≠0)
    (V : (curve K c).Opens) [Nonempty V]
    (e : SheafOfModules.unit V.toScheme.ringCatSheaf ≅ L.object.restrict V.ι)
    (a : Γ(curve K c,V))
    (ha : a * (OpenLineFrameCoordinates318.frame L.object V e V le_rfl).symm
      (L.object.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op s)=0) : a=0 :=
  IntegralLineRestriction318.frame_coordinate_regular L s hs V e a ha
end ContactFieldIntegralLine318
