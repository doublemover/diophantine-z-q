module
public import ContactRelativeFreeCechPresentation318
public import ContactRelativeStructuralHOne318
public section
noncomputable section
namespace ContactRelativeHOneFinitePresentation318
open AlgebraicGeometry CategoryTheory LineSheafClass318 LaurentPolynomial
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactRelativeGeometricTwist318 ContactRelativeGlobalSectionLifting318
open ContactRelativeGeneratorPresentations318 ContactRelativeKernelCoefficientMaps318
open FiniteLaurentVectorFiltration318 ContactRelativeFreeCechPresentation318
set_option maxHeartbeats 950000
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
local instance : Module R (overlapKernel R c L n g) := RelativeLaurentScalar318.coefficientModule R _
local instance : Module R (finiteKernel R c L n g) := Module.compHom _ Polynomial.C
local instance : Module R (infinityKernel R c L n g) := Module.compHom _ Polynomial.C

/-- The original Laurent evaluation kernel is transported only through
the canonical free-source coordinate equivalence. -/
@[expose] def kernelMap : overlapKernel R c L n g →ₗ[R]
    LinearMap.ker (evaluation R c L n g) where
  toFun x := ⟨FreeLaurentPolynomialUnits318.coordinates R ι x,by
    change overlapFiniteEvaluation R c L n g
      ((FreeLaurentPolynomialUnits318.coordinates R ι).symm
        (FreeLaurentPolynomialUnits318.coordinates R ι x)) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact x.property⟩
  map_add' x y := by apply Subtype.ext; exact (FreeLaurentPolynomialUnits318.coordinates R ι).map_add x y
  map_smul' r x := by apply Subtype.ext; exact (FreeLaurentPolynomialUnits318.coordinates R ι).map_smul r x

lemma kernelMap_surjective : Function.Surjective (kernelMap R c L n g) := by
  intro y
  let x : overlapKernel R c L n g :=
    ⟨(FreeLaurentPolynomialUnits318.coordinates R ι).symm y,y.property⟩
  refine ⟨x,?_⟩
  apply Subtype.ext
  exact (FreeLaurentPolynomialUnits318.coordinates R ι).apply_symm_apply y

lemma finite_relation_mem (x : finiteKernel R c L n g) :
    kernelMap R c L n g (finiteMap R c L n g x) ∈
      (positive : Submodule R (V R ι)).comap (LinearMap.ker (evaluation R c L n g)).subtype := by
  change FreeLaurentPolynomialUnits318.coordinates R ι
    (ContactRelativeFiniteKernelLocalization318.restriction R c L n g x) ∈ positive
  rw [finite_value]
  exact FreeLaurentPolynomialUnits318.positive_mem R ι x

lemma infinity_relation_mem (x : infinityKernel R c L n g) :
    kernelMap R c L n g (infinityMap R c L n g x) ∈
      (upper (-(n : ℤ)) : Submodule R (V R ι)).comap
        (LinearMap.ker (evaluation R c L n g)).subtype := by
  change FreeLaurentPolynomialUnits318.coordinates R ι
    ((T (-(n : ℤ)) : LaurentPolynomial R) •
      (ContactRelativeInfinityKernelLocalization318.rawRestriction R c L n g x : ι →₀ LaurentPolynomial R)) ∈ upper (-(n : ℤ))
  rw [FreeLaurentPolynomialUnits318.coordinates_laurent_smul,infinity_value]
  exact FreeLaurentPolynomialUnits318.negative_mem R ι n x

/-- Both actual original relation images are killed by the genuine
free-source Cech boundary. Equality with the full comap boundary is NOT
needed or assumed. -/
lemma relation_boundary (x : overlapKernel R c L n g)
    (hx : x ∈ ContactRelativeFiniteRelationQuotient318.boundary R c L n g) :
    kernelMap R c L n g x ∈ TwoChartFiniteRelations318.kernelBoundary
      (evaluation R c L n g) positive (upper (-(n : ℤ))) := by
  obtain ⟨a,⟨u,rfl⟩,b,⟨v,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add]
  exact Submodule.add_mem _
    ((le_sup_left : _ ≤ TwoChartFiniteRelations318.kernelBoundary
      (evaluation R c L n g) positive (upper (-(n : ℤ)))) (finite_relation_mem R c L n g u))
    ((le_sup_right : _ ≤ TwoChartFiniteRelations318.kernelBoundary
      (evaluation R c L n g) positive (upper (-(n : ℤ)))) (infinity_relation_mem R c L n g v))

/-- The constructed actual relation quotient now supplies finite
relations for the ORIGINAL line Cech quotient. Both image identities,
the free projective source window and the actual kernel surjection are
proved, so no finite-presentation input is left for global H1. -/
theorem quotient_finitePresentation
    (hf : Function.Surjective (finiteEvaluation R c L n g))
    (hi : Function.Surjective (infinityEvaluation R c L n g)) :
    Module.FinitePresentation R (originalSections R c L ⧸
      ContactRelativeOriginalDerivedQuotient318.imageBoundary R c L) := by
  letI : Module.FinitePresentation R
      (V R ι ⧸ ((positive : Submodule R (V R ι)) ⊔ upper (-(n : ℤ)))) :=
    FiniteProjectiveFreeCech318.finitePresentation R ι n
  letI : Module.Finite R ((overlapKernel R c L n g) ⧸
      ContactRelativeFiniteRelationQuotient318.boundary R c L n g) :=
    ContactRelativeFiniteRelationQuotient318.finite R c L n g hf hi
  have h := TwoChartFiniteRelationPresentation318.finitePresentation
    (evaluation R c L n g) positive (upper (-(n : ℤ)))
    (kernelMap R c L n g) (ContactRelativeFiniteRelationQuotient318.boundary R c L n g)
    (relation_boundary R c L n g) (surjective R c L n g hf) (kernelMap_surjective R c L n g)
  rw [finite_image R c L n g hf,infinity_image R c L n g hi] at h
  exact h

local instance : Module R (NonreducedLineMayerVietoris318.H1 L) :=
  OriginalCoefficientCohomology318.cohomologyModule R
    (ContactRelativeStructuralHOne318.projection R c) L 1

/-- ACTUAL original global line H1 is finitely presented over EVERY
coefficient Q-algebra, for the independently defined structural action.
The original whole curve, line, full chart overlap and canonical derived
comparison are retained. Representability of Picard remains separate. -/
theorem finitePresentation_h1 :
    Module.FinitePresentation R (NonreducedLineMayerVietoris318.H1 L) := by
  classical
  obtain ⟨N,hN⟩ := ContactRelativeGeneratorPresentations318.exists_presentations R c L
  obtain ⟨r,s,h,hf,hi,_,_⟩ := hN N le_rfl
  letI := quotient_finitePresentation R c L N h hf hi
  exact Module.FinitePresentation.of_equiv (ContactRelativeStructuralHOne318.equivalence R c L)
end ContactRelativeHOneFinitePresentation318
