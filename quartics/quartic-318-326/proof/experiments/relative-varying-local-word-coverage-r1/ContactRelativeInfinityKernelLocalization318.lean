module
public import ContactRelativeInfinityLaurentPushout318
public import ContactRelativeGeneratorPresentations318
public import OriginalFreePresentationBaseChange318
public import RelativeLaurentModuleShift318
public section
noncomputable section
namespace ContactRelativeInfinityKernelLocalization318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeGeometricTwist318 ContactRelativeGlobalSectionLifting318
open scoped TensorProduct
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (n : ℕ) {ι : Type} (g : ι → Γ((twist R c L (n : ℤ)).object,⊤))
local instance : Algebra (Polynomial R) (LaurentPolynomial R) :=
  LaurentReciprocalTensor318.reciprocalAlgebra R
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom _ (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

/-- The original infinity module is localized with u=t^-1; its section
coordinate is then multiplied by the ACTUAL transition T^n of L(n). -/
@[expose] def shiftedSections : LaurentPolynomial R ⊗[Polynomial R] infinitySections R c L
    ≃ₗ[LaurentPolynomial R] originalSections R c L :=
  (ContactRelativeInfinityLaurentPushout318.sections R c L).trans
    (RelativeLaurentModuleShift318.equivalence R (originalSections R c L) (n : ℤ))

lemma shifted_unit (x : infinitySections R c L) :
    shiftedSections R c L n ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x) =
      (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial R) • infinityRestriction R c L x := by
  change (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial R) •
    ContactRelativeInfinityLaurentPushout318.sections R c L _ = _
  rw [ContactRelativeInfinityLaurentPushout318.sections_unit]

@[expose] def kernelEquivalence {A E F : Type*} [CommRing A]
    [AddCommGroup E] [AddCommGroup F] [Module A E] [Module A F]
    {q q' : E →ₗ[A] F} (h : q = q') : LinearMap.ker q ≃ₗ[A] LinearMap.ker q' := by
  subst q'
  exact LinearEquiv.refl A _

@[expose] def infinityRestriction :
    LinearMap.ker (ContactRelativeGeneratorPresentations318.infinityEvaluation R c L n g) →
      LinearMap.ker (ContactRelativeGeneratorPresentations318.overlapInfinityEvaluation R c L n g) :=
  OriginalFreePresentationBaseChange318.kernelUnit (Polynomial R) (LaurentPolynomial R)
    (infinitySections R c L) (originalSections R c L)
    (shiftedSections R c L n)
    (fun x => (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial R) •
      ContactOriginalRelativeLineOverlap318.infinityRestriction R c L x)
    (shifted_unit R c L n) (fun i => infinityGlobal R c L (n : ℤ) (g i))

lemma infinity_span (hg : Function.Surjective
    (ContactRelativeGeneratorPresentations318.infinityEvaluation R c L n g)) :
    Submodule.span (LaurentPolynomial R) (Set.range (infinityRestriction R c L n g)) = ⊤ :=
  OriginalFreePresentationBaseChange318.kernel_span (Polynomial R) (LaurentPolynomial R)
    (infinitySections R c L) (originalSections R c L)
    (shiftedSections R c L n)
    (fun x => (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial R) •
      ContactOriginalRelativeLineOverlap318.infinityRestriction R c L x)
    (shifted_unit R c L n) (fun i => infinityGlobal R c L (n : ℤ) (g i)) hg

/-- Actual reciprocal polynomial relations land in the SAME finite-side
kernel through the original global-section overlap identity. -/
@[expose] def rawRestriction (x : LinearMap.ker
    (ContactRelativeGeneratorPresentations318.infinityEvaluation R c L n g)) :
    LinearMap.ker (ContactRelativeGeneratorPresentations318.overlapFiniteEvaluation R c L n g) :=
  kernelEquivalence (ContactRelativeGeneratorPresentations318.overlap_evaluation R c L n g).symm
    (infinityRestriction R c L n g x)

lemma raw_span (hg : Function.Surjective
    (ContactRelativeGeneratorPresentations318.infinityEvaluation R c L n g)) :
    Submodule.span (LaurentPolynomial R) (Set.range (rawRestriction R c L n g)) = ⊤ :=
  RelativeLaurentModuleShift318.image_span R
    (LinearMap.ker (ContactRelativeGeneratorPresentations318.overlapInfinityEvaluation R c L n g))
    (kernelEquivalence (ContactRelativeGeneratorPresentations318.overlap_evaluation R c L n g).symm)
    (infinityRestriction R c L n g) (infinity_span R c L n g hg)

/-- The source is O(-n), not O(n): its infinity relation image therefore
has the reciprocal factor T^-n in the common free source module. -/
@[expose] def restriction (x : LinearMap.ker
    (ContactRelativeGeneratorPresentations318.infinityEvaluation R c L n g)) :
    LinearMap.ker (ContactRelativeGeneratorPresentations318.overlapFiniteEvaluation R c L n g) :=
  RelativeLaurentModuleShift318.equivalence R
    (LinearMap.ker (ContactRelativeGeneratorPresentations318.overlapFiniteEvaluation R c L n g))
    (-(n : ℤ)) (rawRestriction R c L n g x)

/-- Both actual chart-kernel images now span ONE original Laurent kernel.
No comparison between two newly chosen abstract kernel presentations occurs. -/
theorem span (hg : Function.Surjective
    (ContactRelativeGeneratorPresentations318.infinityEvaluation R c L n g)) :
    Submodule.span (LaurentPolynomial R) (Set.range (restriction R c L n g)) = ⊤ :=
  RelativeLaurentModuleShift318.shifted_span R
    (LinearMap.ker (ContactRelativeGeneratorPresentations318.overlapFiniteEvaluation R c L n g))
    (rawRestriction R c L n g) (raw_span R c L n g hg) (-(n : ℤ))
end ContactRelativeInfinityKernelLocalization318
