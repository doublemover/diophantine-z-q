module
public import ContactGeneratedHZeroFiber318
public import ContactNormalizedParameterCover318
public section
noncomputable section
namespace ContactGeneratedPositiveFibers318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeGeometricTwist318
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance (M : Line (curve R c)) : Module R Γ(M.object,⊤) :=
  OriginalCoefficientCohomology318.sectionModule R (ContactRelativeStructuralHOne318.projection R c) M ⊤
variable (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2

/-- The previously explicit positive-fiber boundary is PRODUCED from
actual finite-chart generation, at EVERY original scheme residue point.
H1 vanishing alone is not used to infer positivity. -/
theorem positive
    (hg : Submodule.span (R ⊗[ℚ] finiteRing c)
      (Set.range (ContactPositiveChartEvaluation318.finiteRestriction R c L))=⊤) :
    ProjectiveParameterPositiveFibers318.PositiveFibers R Γ(L.object,⊤) := by
  intro x
  let K := (Spec R).residueField x
  let ρ := ProjectiveParameterPositiveFibers318.residueMap R x
  letI : Algebra R K := ρ.hom.toAlgebra
  letI : Algebra ℚ K := (ρ.hom.comp (algebraMap ℚ R)).toAlgebra
  let f : R →ₐ[ℚ] K := { ρ.hom with commutes' := fun _ => rfl }
  exact ContactGeneratedHZeroFiber318.exists_nonzero R K f c L hz hg

/-- Every original relative line admits ONE sufficiently positive twist
whose SAME normalized effective-divisor parameter is a genuine fppf
cover of the original coefficient base. Both vanishing and positive
fibers are now constructed at that index from the original global
sections. This remains a fixed-line Abel presentation, not the whole
varying-line Picard/Jacobian representability theorem. -/
theorem exists_bound : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ h : ∀ x : NonreducedLineMayerVietoris318.H1 (twist R c L (n:ℤ)),x=0,
      Flat (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) ∧
      Surjective (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) ∧
      LocallyOfFinitePresentation
        (ContactNormalizedSectionParameter318.projection R c (twist R c L n) h) := by
  obtain ⟨N,hN⟩ := ContactPositiveChartEvaluation318.exists_bound R c L
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨hv,hg,_⟩ := hN n hn
  refine ⟨hv,?_⟩
  exact ContactNormalizedParameterCover318.flat_surjective_lfp R c (twist R c L n) hv
    (positive R c (twist R c L n) hv hg)
end ContactGeneratedPositiveFibers318
