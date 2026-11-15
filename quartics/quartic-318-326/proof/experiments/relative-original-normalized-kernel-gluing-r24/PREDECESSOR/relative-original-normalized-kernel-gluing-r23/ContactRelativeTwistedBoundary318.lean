module
public import ContactRelativeTwistedCoordinates318
public import RelativeShiftedDifference318
public import NonreducedLineMayerVietoris318
public section
noncomputable section
namespace ContactRelativeTwistedBoundary318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeWholeOpenSections318 ContactRelativeGeometricTwist318
open ContactRelativeTwistedCoordinates318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (d : ℤ)
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L) (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module R (originalSections R c L) :=
  RelativeLaurentScalar318.coefficientModule R (originalSections R c L)
local instance : Module R (finiteSections R c L) := Module.compHom (finiteSections R c L) Polynomial.C
local instance : Module R (infinitySections R c L) := Module.compHom (infinitySections R c L) Polynomial.C

@[expose] def shiftedBoundary := RelativeLaurentGeneratorBound318.boundary R (originalSections R c L)
  (ContactOriginalRelativeOverlapSpan318.finiteMap R c L).range
  (ContactOriginalRelativeOverlapSpan318.infinityMap R c L).range d

/-- The ACTUAL restriction-difference image of the geometric tensor twist
is the exact old shifted Laurent boundary, over every coefficient ring. -/
lemma difference_iff (s : Γ((twist R c L d).object,finiteOpen R c ⊓ infinityOpen R c)) :
    s ∈ (NonreducedLineMayerVietoris318.difference (twist R c L d)
      (finiteOpen R c) (infinityOpen R c)).range ↔
      coordinates R c L d s ∈ shiftedBoundary R c L d := by
  change _ ↔ coordinates R c L d s ∈ RelativeLaurentGeneratorBound318.boundary _ _ _ _ _
  rw [RelativeShiftedDifference318.mem_iff]
  constructor
  · rintro ⟨⟨a,b⟩,hab⟩
    refine ⟨(finiteEquiv R c L).symm (finiteCoordinates R c L d _ le_rfl a),
      (infinityEquiv R c L).symm (infinityCoordinates R c L d _ le_rfl b),?_⟩
    have he := congrArg (coordinates R c L d) hab
    change coordinates R c L d
      ((twist R c L d).object.presheaf.map (homOfLE inf_le_left).op a -
        (twist R c L d).object.presheaf.map (homOfLE inf_le_right).op b) = _ at he
    simpa only [map_sub,finite_restriction,infinity_restriction] using he
  · rintro ⟨a,b,hab⟩
    let a' := (finiteCoordinates R c L d (finiteOpen R c) le_rfl).symm (finiteEquiv R c L a)
    let b' := (infinityCoordinates R c L d (infinityOpen R c) le_rfl).symm (infinityEquiv R c L b)
    refine ⟨(a',b'),?_⟩
    apply (coordinates R c L d).injective
    change coordinates R c L d
      ((twist R c L d).object.presheaf.map (homOfLE inf_le_left).op a' -
        (twist R c L d).object.presheaf.map (homOfLE inf_le_right).op b') = _
    simpa only [map_sub,finite_restriction,infinity_restriction,a',b',
      LinearEquiv.apply_symm_apply,AddEquiv.symm_apply_apply] using hab
end ContactRelativeTwistedBoundary318
