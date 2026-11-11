module
public import OriginalSectionLatticeGeneration318
public section
noncomputable section
namespace OriginalGoodLatticeFrameChange318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open OriginalGoodPlaceCotangentNorms318 OriginalGoodCotangentLattice318
open ContactBicanonicalPointHeight318 FinitePlacePrincipalLattice318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ k, RationalContactPoint318.parameters c t k≠0)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1) (i j : Fin 4)

theorem pair_max_transition :
    max (v (a0 c t hn j)) (v (a1 c t hn j))=
      v (frameScalar c t hn i j)*max (v (a0 c t hn i)) (v (a1 c t hn i)) := by
  rw [frameScalar_a0 c t hn i j,frameScalar_a1 c t hn i j,map_mul,map_mul]
  exact (mul_max_of_nonneg _ _ (v.nonneg (frameScalar c t hn i j))).symm

/-- Correct rational-frame transformation of the actual good-place norms.
The original frame scalar is retained rather than normalized away. -/
theorem norm_transition : finiteNorm c t hn v hv j=
    (v (frameScalar c t hn i j))⁻¹*finiteNorm c t hn v hv i := by
  rw [finiteNorm_eq_max_inverse,finiteNorm_eq_max_inverse,pair_max_transition,mul_inv_rev]
  exact mul_comm _ _

/-- Rational-frame change transports the ACTUAL embedded integral lattice.
Its generators can differ by a local unit; the lattices agree exactly. -/
theorem lattice_transition : modelLattice c t hn v hv j=
    lattice v (frameScalar c t hn i j*normalizer c t hn v hv i) := by
  apply independent_of_generator c t hn v hv j
  · exact mul_ne_zero (frameScalar_ne c t hn i j) (normalizer_ne c t hn v hv i)
  · rw [map_mul,←normalizer_max,pair_max_transition]

/-- Membership transforms by the original rational-frame scalar. This is
an explicit lattice comparison, not only an equality of projective heights. -/
theorem membership_transition (x : K c t) :
    x∈modelLattice c t hn v hv j ↔
      x/frameScalar c t hn i j∈modelLattice c t hn v hv i := by
  rw [mem_iff_bound,mem_iff_bound,norm_transition,map_div₀,div_eq_mul_inv,mul_assoc]
end OriginalGoodLatticeFrameChange318
