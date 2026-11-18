module
public import ContactRelativeOriginalDerivedQuotient318
public import OriginalCoefficientBoundary318
public import OriginalCoefficientImageScalar318
public section
noncomputable section
namespace ContactRelativeStructuralHOne318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativeOverlap318 ContactOriginalRelativePolynomialCharts318
open ContactOriginalRelativeLineOverlap318 ContactRelativeWholeOpenSections318
open scoped TensorProduct
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : IsScalarTower ℚ (LaurentPolynomial ℚ) (oldRing c) where
  smul_assoc q l z := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        simp only [TensorProduct.smul_tmul']
        rw [smul_assoc]
    | add x y hx hy =>
        simp only [smul_add,hx,hy]
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L)
    (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module R (originalSections R c L) :=
  RelativeLaurentScalar318.coefficientModule R (originalSections R c L)
local instance : Module R (finiteSections R c L) := Module.compHom (finiteSections R c L) Polynomial.C
local instance : Module R (infinitySections R c L) := Module.compHom (infinitySections R c L) Polynomial.C

/-- The actual coefficient projection of the original p-first test. -/
abbrev projection := pullback.snd (ContactOriginalAffineTestCover318.p c) (baseMap R)

lemma overlap_over : into R c ≫ projection R c =
    Spec.map (CommRingCat.ofHom (algebraMap R (ring R c))) :=
  RelativeOriginalAffineChart318.over_test (CommRingCat.of ℚ) R (oldRing c)
    (ContactOriginalAffineTestCover318.p c) (oldInto c) (old_over c)

/-- Exact structural coefficient comparison on the ENTIRE original
ambient overlap, not just constant vectors or a generating subset. -/
lemma overlap_scalar (r : R) (x : originalSections R c L) :
    overlapEquiv R c L (r • x) =
      OriginalCoefficientCohomology318.scalar R (projection R c)
        (finiteOpen R c ⊓ infinityOpen R c) r • overlapEquiv R c L x := by
  change overlapEquiv R c L
    (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (C r) • x) = _
  rw [RelativeOriginalLaurentAlgebra318.laurentMap_C]
  letI : Module Γ(Spec (ring R c),⊤) (originalSections R c L) :=
    inferInstanceAs (Module Γ(Spec (ring R c),⊤) Γ((line R c L).object,⊤))
  dsimp only [ContactRelativeWholeOpenSections318.overlapEquiv]
  change L.object.presheaf.map (eqToHom (overlap_image R c).symm).op
    (OriginalOpenPullbackSections318.sectionsEquiv (into R c) L.object
      ((Scheme.ΓSpecIso (ring R c)).inv (algebraMap R (ring R c) r) •
        (x : Γ((line R c L).object,⊤)))) = _
  erw [OriginalOpenPullbackSectionScalar318.scalar,
    OriginalCoefficientImageScalar318.image_scalar R (ring R c) (projection R c) (into R c)
      (CommRingCat.ofHom (algebraMap R (ring R c))) (overlap_over R c)]
  erw [Scheme.Modules.map_smul,OriginalCoefficientCohomology318.scalar_restrict]
  rfl

/-- Structural coefficient action on actual H1 is defined independently
from the Cech quotient, using its genuine module-scalar endomorphisms. -/
local instance : Module R (NonreducedLineMayerVietoris318.H1 L) :=
  OriginalCoefficientCohomology318.cohomologyModule R (projection R c) L 1

/-- The old actual derived boundary is linear for that independent action. -/
def boundaryLinear : originalSections R c L →ₗ[R] NonreducedLineMayerVietoris318.H1 L where
  __ := ContactRelativeOriginalDerivedQuotient318.boundary R c L
  map_smul' r x := by
    dsimp only [ContactRelativeOriginalDerivedQuotient318.boundary]
    change NonreducedLineMayerVietoris318.boundary L (finiteOpen R c) (infinityOpen R c)
      (cover R c) (overlapEquiv R c L (r • x)) = _
    rw [overlap_scalar]
    letI : Module R Γ(L.object,finiteOpen R c ⊓ infinityOpen R c) :=
      OriginalCoefficientCohomology318.sectionModule R (projection R c) L
        (finiteOpen R c ⊓ infinityOpen R c)
    exact (OriginalCoefficientBoundary318.linear R (projection R c) L
      (finiteOpen R c) (infinityOpen R c) (cover R c)).map_smul r (overlapEquiv R c L x)

/-- The existing representative-normalized additive comparison is now
linear for BOTH original actions, rather than defining H1 scalars by
transport across that comparison. -/
@[expose] def equivalence :
    (originalSections R c L ⧸ ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L) ≃ₗ[R]
      NonreducedLineMayerVietoris318.H1 L where
  __ := ContactRelativeOriginalDerivedQuotient318.equivalence R c L
  map_smul' r q := by
    obtain ⟨x,rfl⟩ := (ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L).mkQ_surjective q
    rw [← (ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L).mkQ.map_smul r x]
    change ContactRelativeOriginalDerivedQuotient318.equivalence R c L
      ((ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L).mkQ (r • x)) =
        r • ContactRelativeOriginalDerivedQuotient318.equivalence R c L
          ((ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L).mkQ x)
    rw [ContactRelativeOriginalDerivedQuotient318.equivalence_mk,
      ContactRelativeOriginalDerivedQuotient318.equivalence_mk]
    exact (boundaryLinear R c L).map_smul r x

/-- Genuine finite generation of ACTUAL original global line H1 over
EVERY affine coefficient test, including nonreduced/non-Noetherian ones,
with the original structural R action and original full curve retained.
Further base-change, twist vanishing and representability are separate. -/
theorem finite_h1 : Module.Finite R (NonreducedLineMayerVietoris318.H1 L) := by
  letI := ContactOriginalRelativeFiniteCech318.finite_quotient R c L
  exact Module.Finite.equiv (equivalence R c L)
end ContactRelativeStructuralHOne318
