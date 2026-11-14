module
public import ContactRelativeFiniteRelationQuotient318
public import FreeLaurentPolynomialUnits318
public import TwoChartFiniteRelationPresentation318
public section
noncomputable section
namespace ContactRelativeFreeCechPresentation318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeGeometricTwist318 ContactRelativeGlobalSectionLifting318
open ContactRelativeGeneratorPresentations318 FiniteLaurentVectorFiltration318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
  (g : ι → Γ((twist R c L (n : ℤ)).object,⊤))
local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom _ (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)
local instance : Module R (originalSections R c L) := RelativeLaurentScalar318.coefficientModule R _
local instance : Module R (ι →₀ Polynomial R) := Module.compHom _ Polynomial.C
local instance : Module R (ι →₀ LaurentPolynomial R) := RelativeLaurentScalar318.coefficientModule R _
local instance : Module R (finiteSections R c L) := Module.compHom _ Polynomial.C
local instance : Module R (infinitySections R c L) := Module.compHom _ Polynomial.C

/-- Original common-overlap evaluation with its independently defined
coefficient action, not a new scalar structure transported from a quotient. -/
@[expose] def coefficientEvaluation : (ι →₀ LaurentPolynomial R) →ₗ[R] originalSections R c L where
  toFun := overlapFiniteEvaluation R c L n g
  map_add' := (overlapFiniteEvaluation R c L n g).map_add
  map_smul' r x := (overlapFiniteEvaluation R c L n g).map_smul (C r) x

/-- The actual finite free projective-source Cech map. Its whole-source
coordinates are only the canonical Finsupp/Pi equivalence. -/
@[expose] def evaluation : V R ι →ₗ[R] originalSections R c L :=
  (coefficientEvaluation R c L n g).comp (FreeLaurentPolynomialUnits318.coordinates R ι).symm.toLinearMap

lemma finite_square (x : ι →₀ Polynomial R) :
    evaluation R c L n g (FreeLaurentPolynomialUnits318.positiveUnit R ι x) =
      finiteRestriction R c L (finiteEvaluation R c L n g x) := by
  have h := LinearMap.congr_fun
    (OriginalFreePresentationBaseChange318.square (Polynomial R) (LaurentPolynomial R)
      (finiteSections R c L) (originalSections R c L)
      (ContactRelativeFiniteLaurentPushout318.sections R c L) (finiteRestriction R c L)
      (ContactRelativeFiniteLaurentPushout318.sections_unit R c L)
      (fun i => finiteGlobal R c L (n : ℤ) (g i)))
    ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x)
  change overlapFiniteEvaluation R c L n g (FreeKernelCoefficientMap318.unit R Polynomial.toLaurent x) =
    ContactRelativeFiniteLaurentPushout318.sections R c L
      ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] finiteEvaluation R c L n g x) at h
  rw [ContactRelativeFiniteLaurentPushout318.sections_unit] at h
  change overlapFiniteEvaluation R c L n g
    ((FreeLaurentPolynomialUnits318.coordinates R ι).symm
      (FreeLaurentPolynomialUnits318.coordinates R ι (FreeKernelCoefficientMap318.unit R Polynomial.toLaurent x))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact h

lemma infinity_square (x : ι →₀ Polynomial R) :
    evaluation R c L n g (FreeLaurentPolynomialUnits318.negativeUnit R ι n x) =
      infinityRestriction R c L (infinityEvaluation R c L n g x) := by
  letI : Algebra (Polynomial R) (LaurentPolynomial R) := LaurentReciprocalTensor318.reciprocalAlgebra R
  have h := LinearMap.congr_fun
    (OriginalFreePresentationBaseChange318.square (Polynomial R) (LaurentPolynomial R)
      (infinitySections R c L) (originalSections R c L)
      (ContactRelativeInfinityKernelLocalization318.shiftedSections R c L n)
      (fun y => (T (n : ℤ) : LaurentPolynomial R) • infinityRestriction R c L y)
      (ContactRelativeInfinityKernelLocalization318.shifted_unit R c L n)
      (fun i => infinityGlobal R c L (n : ℤ) (g i)))
    ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] x)
  change overlapInfinityEvaluation R c L n g
    (FreeKernelCoefficientMap318.unit R ((invert (R := R)).toRingHom.comp Polynomial.toLaurent) x) =
    ContactRelativeInfinityKernelLocalization318.shiftedSections R c L n
      ((1 : LaurentPolynomial R) ⊗ₜ[Polynomial R] infinityEvaluation R c L n g x) at h
  rw [← overlap_evaluation,ContactRelativeInfinityKernelLocalization318.shifted_unit] at h
  change overlapFiniteEvaluation R c L n g
    ((FreeLaurentPolynomialUnits318.coordinates R ι).symm
      ((T (-(n : ℤ)) : LaurentPolynomial R) •
        FreeLaurentPolynomialUnits318.coordinates R ι
          (FreeKernelCoefficientMap318.unit R ((invert (R := R)).toRingHom.comp Polynomial.toLaurent) x))) = _
  rw [FreeLaurentPolynomialUnits318.coordinates_symm_laurent_smul,
    LinearEquiv.symm_apply_apply,map_smul,h,smul_smul,← T_add,neg_add_cancel,T_zero,one_smul]

/-- The original finite chart spans, so its actual polynomial surjection
already forces the whole Laurent/free-source map to be surjective. -/
lemma surjective (hf : Function.Surjective (finiteEvaluation R c L n g)) :
    Function.Surjective (evaluation R c L n g) := by
  have hF : Function.Surjective (overlapFiniteEvaluation R c L n g) := by
    apply LinearMap.range_eq_top.mp
    apply top_unique
    rw [← ContactOriginalRelativeOverlapSpan318.finite_span R c L]
    apply Submodule.span_le.mpr
    rintro y ⟨z,rfl⟩
    obtain ⟨x,rfl⟩ := hf z
    exact ⟨(FreeLaurentPolynomialUnits318.coordinates R ι).symm
      (FreeLaurentPolynomialUnits318.positiveUnit R ι x),finite_square R c L n g x⟩
  intro y
  obtain ⟨x,rfl⟩ := hF y
  refine ⟨FreeLaurentPolynomialUnits318.coordinates R ι x,?_⟩
  change overlapFiniteEvaluation R c L n g
    ((FreeLaurentPolynomialUnits318.coordinates R ι).symm
      (FreeLaurentPolynomialUnits318.coordinates R ι x)) = _
  rw [LinearEquiv.symm_apply_apply]
/-- The two source-chart image submodules recover the ACTUAL original
chart images, using the actual chart surjections and both original squares. -/
lemma finite_image (hf : Function.Surjective (finiteEvaluation R c L n g)) :
    (positive : Submodule R (V R ι)).map (evaluation R c L n g) =
      (ContactOriginalRelativeOverlapSpan318.finiteMap R c L).range := by
  rw [← FreeLaurentPolynomialUnits318.positive_range R ι]
  ext y
  constructor
  · rintro ⟨z,⟨x,rfl⟩,rfl⟩
    exact ⟨finiteEvaluation R c L n g x,(finite_square R c L n g x).symm⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨x,rfl⟩ := hf z
    exact ⟨FreeLaurentPolynomialUnits318.positiveUnit R ι x,⟨x,rfl⟩,
      finite_square R c L n g x⟩

lemma infinity_image (hi : Function.Surjective (infinityEvaluation R c L n g)) :
    (upper (-(n : ℤ)) : Submodule R (V R ι)).map (evaluation R c L n g) =
      (ContactOriginalRelativeOverlapSpan318.infinityMap R c L).range := by
  rw [← FreeLaurentPolynomialUnits318.negative_range R ι n]
  ext y
  constructor
  · rintro ⟨z,⟨x,rfl⟩,rfl⟩
    exact ⟨infinityEvaluation R c L n g x,(infinity_square R c L n g x).symm⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨x,rfl⟩ := hi z
    exact ⟨FreeLaurentPolynomialUnits318.negativeUnit R ι n x,⟨x,rfl⟩,
      infinity_square R c L n g x⟩
end ContactRelativeFreeCechPresentation318
