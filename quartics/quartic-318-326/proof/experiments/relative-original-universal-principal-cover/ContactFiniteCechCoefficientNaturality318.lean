module
public import ContactTransportedJetLift318
public import ContactFiniteCechLiftIndependence318
public section
noncomputable section
namespace ContactFiniteCechCoefficientNaturality318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeGeometricTwist318 ContactRelativeFiniteCohomologyModel318
open ContactRelativeFiniteCechComparison318 ContactFiniteComplexCoefficient318
open ContactFiniteCechLiftIndependence318
open scoped TensorProduct
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (b : ℕ)
local instance : Algebra R S := f.toAlgebra
local instance : Module R (finiteSections R c L) := finiteModule R c L
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module S (finiteSections S c (L' R S f c L)) := finiteModule S c _
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance : Module S (originalSections S c (L' R S f c L)) := overlapModule S c _
local instance (N : Line (curve R c)) : Module R Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) N ⊤
local instance (N : Line (curve S c)) : Module S Γ(N.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule S (ContactRelativeStructuralHOne318.projection S c) N ⊤

abbrev transported := ContactTransportedJetLift318.lift R S f c L b
abbrev transported_spec := ContactTransportedJetLift318.specification R S f c L b

lemma original_division (x : termZero R c L b) :
    ContactRelativeInfinityJet318.power R c L b (degreeZero R c L b x).2=
    (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ) x).val.2-
      jetLift R c L b (differential R c L b x) :=
  TwoChartJetChainMap318.division (ContactOriginalRelativeOverlapSpan318.finiteMap R c L)
    (ContactOriginalRelativeOverlapSpan318.infinityMap R c L) (ContactRelativeInfinityJet318.power R c L b)
    (ContactRelativeTwistKernel318.shift R c L ((b+1 : ℕ) : ℤ))
    (ContactRelativeInfinityJet318.injective R c L b) (jetLift R c L b) (jetLift_spec R c L b)
    (ContactRelativeTwistKernel318.globalEquivalence R c L ((b+1 : ℕ) : ℤ) x)

lemma target_division (x : termZero S c (L' R S f c L) b) :
    ContactRelativeInfinityJet318.power S c (L' R S f c L) b
      (otherZero S c (L' R S f c L) b (transported R S f c L b) (transported_spec R S f c L b) x).2=
    (ContactRelativeTwistKernel318.globalEquivalence S c (L' R S f c L) ((b+1 : ℕ) : ℤ) x).val.2-
      transported R S f c L b (differential S c (L' R S f c L) b x) :=
  TwoChartJetChainMap318.division (ContactOriginalRelativeOverlapSpan318.finiteMap S c (L' R S f c L))
    (ContactOriginalRelativeOverlapSpan318.infinityMap S c (L' R S f c L))
    (ContactRelativeInfinityJet318.power S c (L' R S f c L) b)
    (ContactRelativeTwistKernel318.shift S c (L' R S f c L) ((b+1 : ℕ) : ℤ))
    (ContactRelativeInfinityJet318.injective S c (L' R S f c L) b)
    (transported R S f c L b) (transported_spec R S f c L b)
    (ContactRelativeTwistKernel318.globalEquivalence S c (L' R S f c L) ((b+1 : ℕ) : ℤ) x)

/-- Degree one of the transported ORIGINAL comparison is exactly the
comparison built from the transported actual infinity-jet lift. -/
lemma one_square : (otherOne S c (L' R S f c L) b (transported R S f c L b)).comp
    (oneEquivalence R S f c L b).toLinearMap =
    (overlapEquivalence R S f c L).toLinearMap.comp ((degreeOne R c L b).baseChange S) := by
  apply AlgebraTensorModule.ext
  intro s q
  change ContactRelativeTwistKernel318.shift S c (L' R S f c L) ((b+1 : ℕ) : ℤ)
    (ContactOriginalRelativeOverlapSpan318.infinityMap S c (L' R S f c L)
      (transported R S f c L b (oneEquivalence R S f c L b (s ⊗ₜ[R] q))))=_
  rw [ContactTransportedJetLift318.pure_tensor]
  have hg := LinearMap.congr_fun (ContactCoefficientCechBaseChange318.infinity_square R S f c L)
    (s ⊗ₜ[R] jetLift R c L b q)
  have hv := LinearMap.congr_fun (ContactCoefficientCoordinatePowers318.overlap_square R S f c L ((b+1 : ℕ) : ℤ))
    (s ⊗ₜ[R] ContactOriginalRelativeOverlapSpan318.infinityMap R c L (jetLift R c L b q))
  simp only [LinearMap.comp_apply,LinearMap.baseChange_tmul] at hg hv
  rw [← hg]
  exact hv.symm

variable (hz : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L ((b+1 : ℕ) : ℤ)),x=0)

/-- The degree-zero transport follows from the ACTUAL coordinate-power
square and injectivity, retaining the original residual division. -/
lemma zero_square : (otherZero S c (L' R S f c L) b
    (transported R S f c L b) (transported_spec R S f c L b)).comp
    (zeroEquivalence R S f c L b hz).toLinearMap =
    (ContactRelativeHZeroBaseChange318.pairEquivalence R S f c L).toLinearMap.comp
      ((degreeZero R c L b).baseChange S) := by
  apply AlgebraTensorModule.ext
  intro s x
  have hc := zero_coordinates R S f c L b hz s x
  rw [ContactRelativeHZeroBaseChange318.pair_tmul] at hc
  change otherZero S c (L' R S f c L) b (transported R S f c L b) (transported_spec R S f c L b)
    (zeroEquivalence R S f c L b hz (s ⊗ₜ[R] x))=
      ContactRelativeHZeroBaseChange318.pairEquivalence R S f c L (s ⊗ₜ[R] degreeZero R c L b x)
  rw [ContactRelativeHZeroBaseChange318.pair_tmul]
  apply Prod.ext
  · exact congrArg Prod.fst hc
  · apply ContactRelativeInfinityJet318.injective S c (L' R S f c L) b
    rw [target_division]
    have hd := LinearMap.congr_fun (differential_square R S f c L b hz) (s ⊗ₜ[R] x)
    simp only [LinearMap.comp_apply,LinearMap.baseChange_tmul] at hd
    rw [hd,ContactTransportedJetLift318.pure_tensor,congrArg Prod.snd hc]
    have hp := LinearMap.congr_fun (ContactCoefficientCoordinatePowers318.infinity_square R S f c L b)
      (s ⊗ₜ[R] (degreeZero R c L b x).2)
    simp only [LinearMap.comp_apply,LinearMap.baseChange_tmul] at hp
    rw [← hp,original_division,tmul_sub,map_sub]

/-- One ACTUAL homotopy compares the chosen target comparison with the
coefficient transport of the original comparison. It is built from the
literal difference between the chosen and transported infinity lifts. -/
@[expose] def homotopy : termOne S c (L' R S f c L) b →ₗ[S]
    finiteSections S c (L' R S f c L) × infinitySections S c (L' R S f c L) :=
  ContactFiniteCechLiftIndependence318.homotopy S c (L' R S f c L) b
    (transported R S f c L b) (transported_spec R S f c L b)

lemma zero_homotopy : (degreeZero S c (L' R S f c L) b).comp (zeroEquivalence R S f c L b hz).toLinearMap-
    (ContactRelativeHZeroBaseChange318.pairEquivalence R S f c L).toLinearMap.comp ((degreeZero R c L b).baseChange S)=
    (homotopy R S f c L b).comp ((oneEquivalence R S f c L b).toLinearMap.comp
      ((differential R c L b).baseChange S)) := by
  ext x
  have hh := LinearMap.congr_fun (ContactFiniteCechLiftIndependence318.zero_square S c (L' R S f c L) b
    (transported R S f c L b) (transported_spec R S f c L b)) (zeroEquivalence R S f c L b hz x)
  have hz0 := LinearMap.congr_fun (zero_square R S f c L b hz) x
  have hdiff := LinearMap.congr_fun (differential_square R S f c L b hz) x
  simp only [LinearMap.comp_apply] at hz0 hdiff
  simpa only [LinearMap.sub_apply,LinearMap.comp_apply,hz0,hdiff] using hh

lemma one_homotopy : (degreeOne S c (L' R S f c L) b).comp (oneEquivalence R S f c L b).toLinearMap-
    (overlapEquivalence R S f c L).toLinearMap.comp ((degreeOne R c L b).baseChange S)=
    (ContactRelativeCechProjective318.difference S c (L' R S f c L)).comp
      ((homotopy R S f c L b).comp (oneEquivalence R S f c L b).toLinearMap) := by
  ext x
  have hh := LinearMap.congr_fun (ContactFiniteCechLiftIndependence318.one_square S c (L' R S f c L) b
    (transported R S f c L b) (transported_spec R S f c L b)) (oneEquivalence R S f c L b x)
  have h1 := LinearMap.congr_fun (one_square R S f c L b) x
  simp only [LinearMap.comp_apply] at h1
  simpa only [LinearMap.sub_apply,LinearMap.comp_apply,h1] using hh
end ContactFiniteCechCoefficientNaturality318
