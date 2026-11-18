module
public import OriginalMinimalExcludedSections318
public import FinitePlaceTwoSectionGeneration318
public import OriginalFiniteNormAssembly318
public section
noncomputable section
namespace OriginalSectionCotangentComparison318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open ContactBicanonicalPointHeight318 OriginalExcludedPlaceData318
open FinitePlacePrincipalLattice318 FinitePlaceTwoSectionLattice318
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j ≠ 0) (i : Fin 4)

/-- At a place where the arithmetic denominator is a unit, the independently
constructed cotangent-square lattice equals the intrinsic two-section span.
The good-place hypothesis is retained exactly, not extended to excluded places. -/
theorem good_place_equality (v : FinitePlace (K c t))
    (hv : v (denominator c : K c t) = 1) :
    sectionLattice v (a0 c t hn i) (a1 c t hn i) =
      OriginalGoodCotangentLattice318.modelLattice c t hn v hv i := by
  rw [eq_span v _ _ (a0_ne c t hn i)]
  exact OriginalSectionLatticeGeneration318.original_pair_span c t hn v hv i

/-- Exact obstruction at an excluded place: a proposed nonzero geometric
frame generates the section lattice precisely when its norm is the pair
maximum. This criterion does not establish the equality for a geometric frame. -/
theorem excluded_equality_iff (B : ExcludedGenerators c t hn i) (b : BadPlace c t) :
    lattice b.val ((OriginalMinimalExcludedSections318.minimalGenerators c t hn i).generator b) =
      lattice b.val (B.generator b) ↔
    max (b.val (a0 c t hn i)) (b.val (a1 c t hn i)) = b.val (B.generator b) :=
  FinitePlaceTwoSectionGeneration318.eq_iff_max b.val _ _ _
    (a0_ne c t hn i) (B.nonzero b)

/-- The all-place norm is constructed from the actual good-place model and
the minimal section lattices at the finitely many excluded places. It is not
asserted to be the norm of a global geometric Hodge or dualizing model. -/
@[expose] def sectionNorm (v : FinitePlace (K c t)) : ℝ :=
  OriginalFiniteNormAssembly318.finiteNorm c t hn i
    (OriginalMinimalExcludedSections318.minimalGenerators c t hn i) v

theorem sectionNorm_eq (v : FinitePlace (K c t)) : sectionNorm c t hn i v =
    (max (v (a0 c t hn i)) (v (a1 c t hn i)))⁻¹ := by
  unfold sectionNorm OriginalFiniteNormAssembly318.finiteNorm
  split_ifs with hv
  · exact OriginalGoodPlaceCotangentNorms318.finiteNorm_eq_max_inverse c t hn v hv i
  · exact inverse_generator_value v (a0 c t hn i) (a1 c t hn i)

theorem sectionNorm_pos (v : FinitePlace (K c t)) : 0 < sectionNorm c t hn i v :=
  OriginalFiniteNormAssembly318.finiteNorm_pos c t hn i _ v

theorem sectionNorm_finite_support : Function.HasFiniteMulSupport (sectionNorm c t hn i) :=
  OriginalFiniteNormAssembly318.finite_support c t hn i _

/-- Both literal sections are integral for this norm at every finite place.
This establishes section containment, not the absent bad-place KS identity. -/
theorem sectionNorm_bound (v : FinitePlace (K c t)) (n : Fin 2) :
    v (![a0 c t hn i, a1 c t hn i] n) * sectionNorm c t hn i v ≤ 1 :=
  OriginalFiniteNormAssembly318.original_bound c t hn i _ v n

end OriginalSectionCotangentComparison318
