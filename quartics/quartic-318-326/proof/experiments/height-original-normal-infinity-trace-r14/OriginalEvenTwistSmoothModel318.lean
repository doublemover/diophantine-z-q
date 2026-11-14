module
public import OriginalAllPlaceNormalizedData318
public import IntegralOriginalGlobalSmooth318
public import IntegralOriginalProperModel318
public import IntegralValuativePointCenter318
public section
noncomputable section
namespace OriginalEvenTwistSmoothModel318
open NumberField AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : Data c t w) (he : ∀ i,D.exponent i=0)

theorem root_equations (i : Fin 4) : (D.normalizedRoots i)^2=
    algebraMap (V c t w) (K c t) (D.unit i : V c t w) *
      ((t : K c t)-algebraMap (V c t w) (K c t)
        (IntegralSourceBranches318.contacts (V c t w) i)) := by
  simpa [Data.coefficients,he i] using D.root_equation i

/-- Square normalization extends the actual smooth proper integral
model to places where the ORIGINAL twists are nonunits with EVEN
valuation. It does not require the original arithmetic denominator to
be a unit, or the original contact coordinate to be integral. -/
@[expose] def center : Spec (CommRingCat.of (V c t w)) ⟶
    IntegralGluedModel318.scheme (V c t w) D.unit :=
  IntegralValuativePointCenter318.center (V c t w) (K c t) D.unit
    (t : K c t) D.normalizedRoots (root_equations c t w D he)

theorem center_over_base : center c t w D he ≫
    IntegralGluedModel318.structureMap (V c t w) D.unit=𝟙 _ :=
  IntegralValuativePointCenter318.center_over_base _ _ _ _ _ _

theorem center_generic :
    Spec.map (CommRingCat.ofHom (algebraMap (V c t w) (K c t))) ≫ center c t w D he=
      IntegralValuativeGenericPoint318.point (V c t w) (K c t) D.unit
        (t : K c t) D.normalizedRoots (root_equations c t w D he) :=
  IntegralValuativePointCenter318.center_generic _ _ _ _ _ _

theorem proper_smooth
    (h2 : IsUnit (2 : V c t w))
    (hsep : IsUnit (IntegralBranchDenominatorCover318.separationInteger : V c t w)) :
    IsProper (IntegralGluedModel318.structureMap (V c t w) D.unit) ∧
    Smooth (IntegralGluedModel318.structureMap (V c t w) D.unit) :=
  ⟨(IntegralOriginalProperModel318.proper_separated (V c t w) D.unit).1,
    IntegralOriginalGlobalSmooth318.smooth (V c t w) D.unit h2 hsep⟩

/-- Scaling back identifies each exact original source generator value,
including its sign. The model is not substituted by an unrelated curve. -/
theorem original_roots (i : Fin 4) : D.multiplier i * D.normalizedRoots i =
    RationalContactPoint318.sourcePoint c t
      (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) i) :=
  D.original_signed_root i
end OriginalEvenTwistSmoothModel318
