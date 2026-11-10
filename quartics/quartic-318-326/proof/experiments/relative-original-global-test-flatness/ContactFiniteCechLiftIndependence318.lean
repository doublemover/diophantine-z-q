module
public import ContactRelativeFiniteCechComparison318
public import TwoChartJetLiftHomotopy318
public section
noncomputable section
namespace ContactFiniteCechLiftIndependence318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactRelativeGeometricTwist318
open ContactOriginalRelativeOverlapSpan318 ContactRelativeFiniteCohomologyModel318
open ContactRelativeFiniteCechComparison318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (b : ℕ)
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
variable (s : termOne R c L b →ₗ[R] infinitySections R c L)
  (hs : (ContactRelativeInfinityJet318.power R c L b).range.mkQ.comp s=LinearMap.id)

@[expose] def otherZero : termZero R c L b →ₗ[R] finiteSections R c L × infinitySections R c L :=
  (TwoChartJetChainMap318.degreeZero (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (ContactRelativeInfinityJet318.injective R c L b) s hs).comp
    (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ)).toLinearMap
@[expose] def otherOne : termOne R c L b →ₗ[R] originalSections R c L :=
  TwoChartJetChainMap318.degreeOne (infinityMap R c L) (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ)) s

@[expose] def homotopy : termOne R c L b →ₗ[R] finiteSections R c L × infinitySections R c L :=
  TwoChartJetLiftHomotopy318.homotopy (A := finiteSections R c L)
    (ContactRelativeInfinityJet318.power R c L b) (ContactRelativeInfinityJet318.injective R c L b)
    (jetLift R c L b) s (jetLift_spec R c L b) hs

/-- Changing the actual jet lift changes the ACTUAL degree-zero original
Cech map by the exhibited homotopy times the same finite differential. -/
lemma zero_square : degreeZero R c L b-otherZero R c L b s hs =
    (homotopy R c L b s hs).comp (differential R c L b) := by
  ext x
  exact LinearMap.congr_fun (TwoChartJetLiftHomotopy318.zero_square
    (finiteMap R c L) (infinityMap R c L) (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (ContactRelativeInfinityJet318.injective R c L b) (jetLift R c L b) s
    (jetLift_spec R c L b) hs) (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ) x)

/-- The same homotopy also gives the actual degree-one square. Thus this
particular auxiliary lift cannot change the original derived comparison. -/
lemma one_square : degreeOne R c L b-otherOne R c L b s =
    (ContactRelativeCechProjective318.difference R c L).comp (homotopy R c L b s hs) :=
  TwoChartJetLiftHomotopy318.one_square (finiteMap R c L) (infinityMap R c L)
    (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (original_power R c L b) (ContactRelativeInfinityJet318.injective R c L b)
    (jetLift R c L b) s (jetLift_spec R c L b) hs
end ContactFiniteCechLiftIndependence318
