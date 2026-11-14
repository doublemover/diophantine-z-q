module
public import OriginalAnisotropicRectangle318
public section
noncomputable section
namespace OriginalDeterminantMinima318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalAttainedMinima318
open OriginalIntegerNormalProjection318 OriginalNormalHeightGenerator318 OriginalPlaneRounding318
open OriginalControlledIntegralBasis318 OriginalCofactorCoordinates318
set_option maxHeartbeats 5000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quantitative nondegeneracy of the actual first two shortest vectors.
It is the ORIGINAL cross product and metric, not an assumed basis angle. -/
lemma gram_lower (u v : Vector ℤ) (huv : ‖embed u‖≤‖embed v‖)
    (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2) :
    ‖embed u‖^2*‖embed v‖^2/4≤(dot (normal u v) (normal u v):ℝ) := by
  have hu := inner_embed u u
  have hv := inner_embed v v
  have huv' := inner_embed u v
  rw [real_inner_self_eq_norm_sq] at hu hv
  have hnorm : (dot (normal u v) (normal u v):ℝ)=
      ‖embed u‖^2*‖embed v‖^2-⟪embed u,embed v⟫^2 := by
    have hh : (dot (normal u v) (normal u v):ℝ)=
        (dot u u:ℝ)*(dot v v:ℝ)-(dot u v:ℝ)^2 := by exact_mod_cast normal_length u v
    rwa [←hu,←hv,←huv'] at hh
  have hp := mul_self_le_mul_self (abs_nonneg ⟪embed u,embed v⟫) hip
  have hUV := pow_le_pow_left₀ (norm_nonneg _) huv 2
  have hprod := mul_le_mul_of_nonneg_left hUV (sq_nonneg ‖embed u‖)
  rw [hnorm]
  nlinarith [sq_abs ⟪embed u,embed v⟫]

/-- Nearest-plane rounding of the actual whole-basis third vector retains
its nonzero normal value. Actual THIRD minimality bounds its normal
height below, so thin/sheared bases cannot evade the inverse rectangle. -/
theorem actual_determinant_lower (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple p κ t u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2)
    (hwmin : ∀ y : Vector ℤ, y∈literalLattice p κ t →
      embed y∉Submodule.span ℝ (Set.range ![embed u,embed v]) → ‖embed w‖≤‖embed y‖) :
    ‖embed u‖*‖embed v‖*‖embed w‖≤4*|(determinant u v z:ℝ)| := by
  have hn := normal_ne_zero u v (hb.1.2.ne_zero 0) huv hip
  have hd := determinant_ne_zero p hp κ t u v z hb huv hip
  let n := normal u v
  let D : ℝ := (dot n n:ℝ)
  have hD : 0<D := by exact_mod_cast dot_self_positive n hn
  let a := coefficientA u v z
  let b := coefficientB u v z
  let r := reduced u v z a b
  have hr : r∈literalLattice p κ t := reduced_mem p κ t u v z
    (hb.1.1 0) (hb.1.1 1) (hb.1.1 2) a b
  have hnr : dot n r=determinant u v z := by
    exact reduced_normal_value n u v z (normal_dot_left u v) (normal_dot_right u v) a b
  let K : Submodule ℝ E := (innerSL ℝ (embed n)).toLinearMap.ker
  have hplane : Submodule.span ℝ (Set.range ![embed u,embed v])≤K := by
    apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    fin_cases i
    · change ⟪embed n,embed u⟫=0
      rw [inner_embed,normal_dot_left,Int.cast_zero]
    · change ⟪embed n,embed v⟫=0
      rw [inner_embed,normal_dot_right,Int.cast_zero]
  have hrout : embed r∉Submodule.span ℝ (Set.range ![embed u,embed v]) := by
    intro hh
    have he := hplane hh
    change ⟪embed n,embed r⟫=0 at he
    rw [inner_embed,hnr] at he
    apply hd
    exact_mod_cast he
  have hmin := hwmin r hr hrout
  have hminsq := pow_le_pow_left₀ (norm_nonneg _) hmin 2
  have horth := normal_orthogonal u v z
  have hround := actual_rounding_bound u v z (normalComponent u v z) a b
    (actual_decomposition u v z hn) horth.1 horth.2 huv hip
  rw [normal_component_norm_sq u v z hn] at hround
  change ‖embed r‖^2≤(determinant u v z:ℝ)^2/D+(3/4:ℝ)*‖embed v‖^2 at hround
  have hVW := pow_le_pow_left₀ (norm_nonneg _) hvw 2
  have hheight : ‖embed w‖^2/4≤(determinant u v z:ℝ)^2/D := by nlinarith
  have hheight' := (le_div_iff₀ hD).mp hheight
  have hgram := gram_lower u v huv hip
  have hmul := mul_le_mul_of_nonneg_left hgram (show 0≤‖embed w‖^2/4 by positivity)
  have hnonneg : 0≤‖embed u‖*‖embed v‖*‖embed w‖ := by positivity
  change ‖embed w‖^2/4*(‖embed u‖^2*‖embed v‖^2/4)≤‖embed w‖^2/4*D at hmul
  have hs : (‖embed u‖*‖embed v‖*‖embed w‖)^2≤
      (4*|(determinant u v z:ℝ)|)^2 := by
    nlinarith [sq_abs (determinant u v z:ℝ)]
  exact (sq_le_sq₀ hnonneg (by positivity)).mp hs

end OriginalDeterminantMinima318
