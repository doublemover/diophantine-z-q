module
public import ContactOriginalRelativeFiniteCech318
public import ContactRelativeWholeOpenSections318
public import NonreducedLineMayerVietoris318
public import OriginalTwoImageBoundary318
public section
noncomputable section
namespace ContactRelativeOriginalDerivedQuotient318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativeOverlap318 ContactOriginalRelativePolynomialCharts318
open ContactOriginalRelativeLineOverlap318 ContactRelativeWholeOpenSections318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L)
    (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module R (originalSections R c L) :=
  RelativeLaurentScalar318.coefficientModule R (originalSections R c L)
local instance : Module R (finiteSections R c L) :=
  Module.compHom (finiteSections R c L) Polynomial.C
local instance : Module R (infinitySections R c L) :=
  Module.compHom (infinitySections R c L) Polynomial.C

/-- The same original finite/infinity image boundary as in the finite
coefficient-quotient theorem, without replacing its carrier or actions. -/
abbrev imageBoundary : Submodule R (originalSections R c L) :=
  (ContactOriginalRelativeOverlapSpan318.finiteMap R c L).range ⊔
    (ContactOriginalRelativeOverlapSpan318.infinityMap R c L).range

/-- The ACTUAL original global derived boundary, now on the actual
Laurent sections via the proved full ambient overlap comparison. -/
def boundary : originalSections R c L →+ NonreducedLineMayerVietoris318.H1 L :=
  (NonreducedLineMayerVietoris318.boundary L (finiteOpen R c) (infinityOpen R c) (cover R c)).comp
    (overlapEquiv R c L).toAddMonoidHom

lemma boundary_surjective : Function.Surjective (boundary R c L) :=
  (NonreducedLineMayerVietoris318.boundary_surjective L (finiteOpen R c) (infinityOpen R c)
    (finite_affine R c) (infinity_affine R c) (cover R c)).comp (overlapEquiv R c L).surjective

/-- The kernel is exactly the old actual two-image boundary. Both
full-chart comparison squares are used in BOTH directions. -/
lemma kernel_eq_image : (boundary R c L).ker = (imageBoundary R c L).toAddSubgroup := by
  ext x
  change boundary R c L x = 0 ↔ x ∈ imageBoundary R c L
  have hk : NonreducedLineMayerVietoris318.boundary L (finiteOpen R c) (infinityOpen R c)
        (cover R c) (overlapEquiv R c L x) = 0 ↔
      ∃ y, NonreducedLineMayerVietoris318.difference L (finiteOpen R c) (infinityOpen R c) y =
        overlapEquiv R c L x := by
    change overlapEquiv R c L x ∈
        (NonreducedLineMayerVietoris318.boundary L (finiteOpen R c) (infinityOpen R c) (cover R c)).ker ↔ _
    rw [NonreducedLineMayerVietoris318.kernel_eq_range]
    rfl
  constructor
  · intro hx
    obtain ⟨⟨a,b⟩,hab⟩ := hk.mp hx
    apply (OriginalTwoImageBoundary318.mem_iff
      (ContactOriginalRelativeOverlapSpan318.finiteMap R c L)
      (ContactOriginalRelativeOverlapSpan318.infinityMap R c L) x).mpr
    refine ⟨(finiteEquiv R c L).symm a,(infinityEquiv R c L).symm b,?_⟩
    apply (overlapEquiv R c L).injective
    change overlapEquiv R c L
      (finiteRestriction R c L ((finiteEquiv R c L).symm a) -
        infinityRestriction R c L ((infinityEquiv R c L).symm b)) = _
    rw [map_sub,finite_square,infinity_square,AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
    simpa [NonreducedLineMayerVietoris318.difference] using hab
  · intro hx
    obtain ⟨a,b,hab⟩ := (OriginalTwoImageBoundary318.mem_iff
      (ContactOriginalRelativeOverlapSpan318.finiteMap R c L)
      (ContactOriginalRelativeOverlapSpan318.infinityMap R c L) x).mp hx
    apply hk.mpr
    refine ⟨(finiteEquiv R c L a,infinityEquiv R c L b),?_⟩
    dsimp only [NonreducedLineMayerVietoris318.difference]
    change L.object.presheaf.map (homOfLE inf_le_left :
        finiteOpen R c ⊓ infinityOpen R c ⟶ finiteOpen R c).op (finiteEquiv R c L a) -
      L.object.presheaf.map (homOfLE inf_le_right :
        finiteOpen R c ⊓ infinityOpen R c ⟶ infinityOpen R c).op (infinityEquiv R c L b) = _
    rw [← finite_square,← infinity_square,← map_sub]
    exact congrArg (overlapEquiv R c L) hab

/-- The exact original coefficient Cech quotient, already proved finite
over R, is additively the ACTUAL derived H1 of the SAME original line on
the complete test curve. No replacement curve, sheaf or quotient occurs.
We do not transport an arbitrary module action onto H1: matching its
structural R action and further base-change remains separate. -/
def equivalence : (originalSections R c L ⧸ imageBoundary R c L) ≃+
    NonreducedLineMayerVietoris318.H1 L :=
  (QuotientAddGroup.quotientAddEquivOfEq (kernel_eq_image R c L).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (boundary R c L) (boundary_surjective R c L))

/-- On every original overlap representative, the comparison is literally
the original derived Mayer-Vietoris boundary, not an arbitrary additive
isomorphism between the two underlying groups. -/
lemma equivalence_mk (x : originalSections R c L) :
    equivalence R c L ((imageBoundary R c L).mkQ x) = boundary R c L x := rfl
end ContactRelativeOriginalDerivedQuotient318
