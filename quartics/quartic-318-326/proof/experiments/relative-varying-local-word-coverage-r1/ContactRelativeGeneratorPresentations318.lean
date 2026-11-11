module
public import ContactRelativeGlobalGenerators318
public import ContactRelativeChartFinitePresentation318
public section
noncomputable section
namespace ContactRelativeGeneratorPresentations318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeGeometricTwist318
open ContactOriginalRelativeLineOverlap318
open ContactRelativeGlobalSectionLifting318
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c)) (n : ℕ)
variable {ι : Type} (g : ι → Γ((twist R c L (n : ℤ)).object,⊤))

/-- Original polynomial-chart evaluations of the SAME global sections,
expressed in the proved original untwisting coordinates. -/
@[expose] def finiteEvaluation : (ι →₀ Polynomial R) →ₗ[Polynomial R] finiteSections R c L :=
  Finsupp.linearCombination (Polynomial R) (fun i => finiteGlobal R c L (n : ℤ) (g i))
@[expose] def infinityEvaluation : (ι →₀ Polynomial R) →ₗ[Polynomial R] infinitySections R c L :=
  Finsupp.linearCombination (Polynomial R) (fun i => infinityGlobal R c L (n : ℤ) (g i))

local instance : Module (LaurentPolynomial R) (originalSections R c L) :=
  Module.compHom (originalSections R c L) (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c)

@[expose] def overlapFiniteEvaluation : (ι →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
    originalSections R c L :=
  Finsupp.linearCombination (LaurentPolynomial R)
    (fun i => finiteRestriction R c L (finiteGlobal R c L (n : ℤ) (g i)))
@[expose] def overlapInfinityEvaluation : (ι →₀ LaurentPolynomial R) →ₗ[LaurentPolynomial R]
    originalSections R c L :=
  Finsupp.linearCombination (LaurentPolynomial R)
    (fun i => (LaurentPolynomial.T (n : ℤ) : LaurentPolynomial R) •
      infinityRestriction R c L (infinityGlobal R c L (n : ℤ) (g i)))

/-- The two finite presentations come from ONE actual full-overlap map,
not independently chosen polynomial surjections. -/
lemma overlap_evaluation : overlapFiniteEvaluation R c L n g = overlapInfinityEvaluation R c L n g := by
  apply congrArg (Finsupp.linearCombination (LaurentPolynomial R))
  funext i
  exact global_relation R c L (n : ℤ) (g i)

/-- A single finite global family gives surjective presentations on BOTH
whole polynomial charts, with finitely generated kernels. Kernel finiteness
uses actual target FINITE PRESENTATION, not just its finite generation. -/
theorem exists_presentations : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ (r s : ℕ) (g : Fin r ⊕ Fin s → Γ((twist R c L (n : ℤ)).object,⊤)),
      Function.Surjective (finiteEvaluation R c L n g) ∧
      Function.Surjective (infinityEvaluation R c L n g) ∧
      (LinearMap.ker (finiteEvaluation R c L n g)).FG ∧
      (LinearMap.ker (infinityEvaluation R c L n g)).FG := by
  obtain ⟨N,hN⟩ := ContactRelativeGlobalGenerators318.exists_generators R c L
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨r,s,a,b,ha,hb⟩ := hN n hn
  let g : Fin r ⊕ Fin s → Γ((twist R c L (n : ℤ)).object,⊤) := Sum.elim a b
  have hfinite : Submodule.span (Polynomial R)
      (Set.range (fun i => finiteGlobal R c L (n : ℤ) (g i))) = ⊤ := by
    apply top_unique
    rw [← ha]
    apply Submodule.span_mono
    rintro x ⟨i,rfl⟩
    exact ⟨Sum.inl i,rfl⟩
  have hinfinity : Submodule.span (Polynomial R)
      (Set.range (fun i => infinityGlobal R c L (n : ℤ) (g i))) = ⊤ := by
    apply top_unique
    rw [← hb]
    apply Submodule.span_mono
    rintro x ⟨i,rfl⟩
    exact ⟨Sum.inr i,rfl⟩
  have hf : Function.Surjective (finiteEvaluation R c L n g) :=
    LinearMap.range_eq_top.mp (by
      rw [finiteEvaluation,Finsupp.range_linearCombination]
      exact hfinite)
  have hi : Function.Surjective (infinityEvaluation R c L n g) :=
    LinearMap.range_eq_top.mp (by
      rw [infinityEvaluation,Finsupp.range_linearCombination]
      exact hinfinity)
  letI : Module.FinitePresentation (Polynomial R) (finiteSections R c L) :=
    ContactRelativeChartFinitePresentation318.finite_chart R c L
  letI : Module.FinitePresentation (Polynomial R) (infinitySections R c L) :=
    ContactRelativeChartFinitePresentation318.infinity_chart R c L
  exact ⟨r,s,g,hf,hi,Module.FinitePresentation.fg_ker _ hf,Module.FinitePresentation.fg_ker _ hi⟩
end ContactRelativeGeneratorPresentations318
