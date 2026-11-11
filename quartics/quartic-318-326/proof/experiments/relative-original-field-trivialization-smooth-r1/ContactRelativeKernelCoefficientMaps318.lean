module
public import ContactRelativeFiniteKernelLocalization318
public import ContactRelativeInfinityKernelLocalization318
public import FreeKernelCoefficientMap318
public section
noncomputable section
namespace ContactRelativeKernelCoefficientMaps318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeGeometricTwist318 ContactRelativeGlobalSectionLifting318
open ContactRelativeGeneratorPresentations318
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (n : ℕ) {ι : Type} (g : ι → Γ((twist R c L (n : ℤ)).object,⊤))
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom _ (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

abbrev finiteKernel := LinearMap.ker (finiteEvaluation R c L n g)
abbrev infinityKernel := LinearMap.ker (infinityEvaluation R c L n g)
abbrev overlapKernel := LinearMap.ker (overlapFiniteEvaluation R c L n g)
local instance : Module R (finiteKernel R c L n g) := Module.compHom _ Polynomial.C
local instance : Module R (infinityKernel R c L n g) := Module.compHom _ Polynomial.C
local instance : Module R (overlapKernel R c L n g) :=
  RelativeLaurentScalar318.coefficientModule R _

lemma finite_value (x : finiteKernel R c L n g) :
    (ContactRelativeFiniteKernelLocalization318.restriction R c L n g x : ι →₀ LaurentPolynomial R) =
      FreeKernelCoefficientMap318.unit R Polynomial.toLaurent x := rfl

@[expose] def finiteMap : finiteKernel R c L n g →ₗ[R] overlapKernel R c L n g :=
  FreeKernelCoefficientMap318.map R Polynomial.toLaurent _ _
    (ContactRelativeFiniteKernelLocalization318.restriction R c L n g)
    (finite_value R c L n g) (fun r => Polynomial.toLaurent_C r)

lemma finite_polynomial (p : Polynomial R) (x : finiteKernel R c L n g) :
    finiteMap R c L n g (p • x) = (Polynomial.toLaurent p : LaurentPolynomial R) • finiteMap R c L n g x :=
  FreeKernelCoefficientMap318.polynomial R Polynomial.toLaurent _ _
    (ContactRelativeFiniteKernelLocalization318.restriction R c L n g)
    (finite_value R c L n g) p x

lemma kernelEquivalence_value {A E F : Type*} [CommRing A]
    [AddCommGroup E] [AddCommGroup F] [Module A E] [Module A F]
    {q q' : E →ₗ[A] F} (h : q = q') (x : LinearMap.ker q) :
    (ContactRelativeInfinityKernelLocalization318.kernelEquivalence h x : E) = x := by
  subst q'
  rfl

lemma infinity_value (x : infinityKernel R c L n g) :
    (ContactRelativeInfinityKernelLocalization318.rawRestriction R c L n g x : ι →₀ LaurentPolynomial R) =
      FreeKernelCoefficientMap318.unit R
        ((LaurentPolynomial.invert (R := R)).toRingHom.comp Polynomial.toLaurent) x := by
  rw [ContactRelativeInfinityKernelLocalization318.rawRestriction,kernelEquivalence_value]
  rfl

@[expose] def rawInfinityMap : infinityKernel R c L n g →ₗ[R] overlapKernel R c L n g :=
  FreeKernelCoefficientMap318.map R
    ((LaurentPolynomial.invert (R := R)).toRingHom.comp Polynomial.toLaurent) _ _
    (ContactRelativeInfinityKernelLocalization318.rawRestriction R c L n g)
    (infinity_value R c L n g)
    (fun r => by rw [RingHom.comp_apply,Polynomial.toLaurent_C,LaurentPolynomial.invert_C])

/-- The actual O(-n) source-coordinate transition is preserved at the
coefficient-linear relation-map level. -/
@[expose] def infinityMap : infinityKernel R c L n g →ₗ[R] overlapKernel R c L n g :=
  (RelativeLaurentScalar318.shift R (overlapKernel R c L n g) (-(n : ℤ))).comp
    (rawInfinityMap R c L n g)

lemma infinity_polynomial (p : Polynomial R) (x : infinityKernel R c L n g) :
    infinityMap R c L n g (p • x) =
      (LaurentPolynomial.invert (Polynomial.toLaurent p) : LaurentPolynomial R) • infinityMap R c L n g x := by
  have h := FreeKernelCoefficientMap318.polynomial R
    ((LaurentPolynomial.invert (R := R)).toRingHom.comp Polynomial.toLaurent) _ _
    (ContactRelativeInfinityKernelLocalization318.rawRestriction R c L n g)
    (infinity_value R c L n g) p x
  change (LaurentPolynomial.T (-(n : ℤ)) : LaurentPolynomial R) •
    ContactRelativeInfinityKernelLocalization318.rawRestriction R c L n g (p • x) = _
  rw [h]
  exact smul_comm _ _ _

lemma finite_span (hg : Function.Surjective (finiteEvaluation R c L n g)) :
    Submodule.span (LaurentPolynomial R) ((finiteMap R c L n g).range : Set (overlapKernel R c L n g)) = ⊤ := by
  change Submodule.span (LaurentPolynomial R)
    (Set.range (ContactRelativeFiniteKernelLocalization318.restriction R c L n g)) = ⊤
  exact ContactRelativeFiniteKernelLocalization318.span R c L n g hg

lemma infinity_span (hg : Function.Surjective (infinityEvaluation R c L n g)) :
    Submodule.span (LaurentPolynomial R) ((infinityMap R c L n g).range : Set (overlapKernel R c L n g)) = ⊤ := by
  change Submodule.span (LaurentPolynomial R)
    (Set.range (ContactRelativeInfinityKernelLocalization318.restriction R c L n g)) = ⊤
  exact ContactRelativeInfinityKernelLocalization318.span R c L n g hg
end ContactRelativeKernelCoefficientMaps318
