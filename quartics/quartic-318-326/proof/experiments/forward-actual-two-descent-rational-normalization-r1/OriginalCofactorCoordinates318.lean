module
public import OriginalWholeBasisCoordinates318
public section
noncomputable section
namespace OriginalCofactorCoordinates318
open scoped BigOperators RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalIntegerNormalProjection318
open OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def determinant (u v z : Vector ℤ) : ℤ := dot (normal u v) z

lemma cofactor_first (u v z c : Vector ℤ) :
    dot (normal v z) (synthesis u v z c)=determinant u v z*c.1 := by
  dsimp [synthesis,determinant,normal,dot]
  simp only [zsmul_eq_mul]
  ring
lemma cofactor_second (u v z c : Vector ℤ) :
    dot (normal z u) (synthesis u v z c)=determinant u v z*c.2.1 := by
  dsimp [synthesis,determinant,normal,dot]
  simp only [zsmul_eq_mul]
  ring
lemma cofactor_third (u v z c : Vector ℤ) :
    dot (normal u v) (synthesis u v z c)=determinant u v z*c.2.2 := by
  dsimp [synthesis,determinant,normal,dot]
  simp only [zsmul_eq_mul]
  ring

/-- Nonzero determinant is deduced from whole-lattice integer spanning
and the original modulus axes. No index/determinant formula is presumed. -/
theorem determinant_ne_zero (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple p κ t u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2) :
    determinant u v z≠0 := by
  have hn := normal_ne_zero u v (hb.1.2.ne_zero 0) huv hip
  intro hd
  have hz (y : Vector ℤ) (hy : y∈literalLattice p κ t) : dot (normal u v) y=0 := by
    obtain ⟨a,b,c,hc⟩ := hb.2 y hy
    have hh := cofactor_third u v z (a,b,c)
    change dot (normal u v) (a • u+b • v+c • z)=determinant u v z*c at hh
    rw [←hc,hd,zero_mul] at hh
    exact hh
  let M : ℤ := FixedSquarefreeCRT318.modulus p
  have hM : M≠0 := by
    have hh := FixedSquarefreeCRT318.modulus_positive p hp
    exact_mod_cast (ne_of_gt hh)
  have hx := hz (M,0,0) (by simpa [M] using modulus_multiple_mem p κ t (1,0,0))
  have hy := hz (0,M,0) (by simpa [M] using modulus_multiple_mem p κ t (0,1,0))
  have hz' := hz (0,0,M) (by simpa [M] using modulus_multiple_mem p κ t (0,0,1))
  simp only [dot,mul_zero,mul_one,zero_add,add_zero] at hx hy hz'
  apply hn
  exact Prod.ext ((mul_eq_zero.mp hx).resolve_right hM)
    (Prod.ext ((mul_eq_zero.mp hy).resolve_right hM) ((mul_eq_zero.mp hz').resolve_right hM))

/-- The actual inverse coefficients are cofactor ratios, but are already
integers by wholeEquiv; rational Cramer's rule is not used as integrality. -/
theorem inverse_cofactor_identities (p : ι → ℕ) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) (u v z : Vector ℤ)
    (hb : IntegralBasisTriple p κ t u v z) (y : literalLattice p κ t) :
    let c := (wholeEquiv p κ t u v z hb).symm y
    dot (normal v z) y=determinant u v z*c.1 ∧
    dot (normal z u) y=determinant u v z*c.2.1 ∧
    dot (normal u v) y=determinant u v z*c.2.2 := by
  dsimp only
  rw [←wholeEquiv_inverse p κ t u v z hb y]
  exact ⟨cofactor_first _ _ _ _,cofactor_second _ _ _ _,cofactor_third _ _ _ _⟩

lemma cross_norm_le (u v : Vector ℤ) : ‖embed (normal u v)‖≤‖embed u‖*‖embed v‖ := by
  have hn := inner_embed (normal u v) (normal u v)
  have hu := inner_embed u u
  have hv := inner_embed v v
  rw [real_inner_self_eq_norm_sq] at hn hu hv
  have hh : (dot (normal u v) (normal u v):ℝ)=
      (dot u u:ℝ)*(dot v v:ℝ)-(dot u v:ℝ)^2 := by exact_mod_cast normal_length u v
  rw [←hn,←hu,←hv] at hh
  have hprod := mul_nonneg (norm_nonneg (embed u)) (norm_nonneg (embed v))
  nlinarith [norm_nonneg (embed (normal u v)),sq_nonneg (dot u v:ℝ)]

/-- Exact original-coordinate inverse bound; the numerator uses the two
OTHER basis lengths. This is the anisotropic Cramer rectangle, not a
single cubic box replacing all three scales by the longest vector. -/
lemma coefficient_bound (n y : Vector ℤ) (D c : ℤ) (hD : D≠0)
    (hc : dot n y=D*c) (R : ℝ) (hR : ‖embed y‖≤R) :
    |(c:ℝ)|≤R*‖embed n‖/|(D:ℝ)| := by
  have hDr : (D:ℝ)≠0 := by exact_mod_cast hD
  have hc' : ⟪embed n,embed y⟫=(D:ℝ)*(c:ℝ) := by
    rw [inner_embed,hc,Int.cast_mul]
  have hh := abs_real_inner_le_norm (embed n) (embed y)
  rw [hc',abs_mul] at hh
  have hR' := mul_le_mul_of_nonneg_left hR (norm_nonneg (embed n))
  apply (le_div_iff₀ (abs_pos.mpr hDr)).mpr
  nlinarith

end OriginalCofactorCoordinates318
