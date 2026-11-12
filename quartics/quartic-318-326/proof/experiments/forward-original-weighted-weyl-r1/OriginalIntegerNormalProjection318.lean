module
public import OriginalSequentialMinima318
public section
noncomputable section
namespace OriginalIntegerNormalProjection318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralIntegerDuality318 OriginalEuclideanLattice318
open OriginalNormalHeightGenerator318
set_option maxHeartbeats 4000000

@[expose] def normal (u v : Vector ℤ) : Vector ℤ :=
  (u.2.1*v.2.2-u.2.2*v.2.1,u.2.2*v.1-u.1*v.2.2,u.1*v.2.1-u.2.1*v.1)

lemma normal_dot_left (u v : Vector ℤ) : dot (normal u v) u=0 := by dsimp [normal,dot]; ring
lemma normal_dot_right (u v : Vector ℤ) : dot (normal u v) v=0 := by dsimp [normal,dot]; ring
lemma dot_comm (u v : Vector ℤ) : dot u v=dot v u := by dsimp [dot]; ring
lemma normal_length (u v : Vector ℤ) :
    dot (normal u v) (normal u v)=dot u u*dot v v-(dot u v)^2 := by dsimp [normal,dot]; ring

/-- Reduction gives a quantitative positive Gram determinant, so the
integer cross-product normal is genuinely nonzero. -/
lemma normal_ne_zero (u v : Vector ℤ) (hu : embed u≠0)
    (huv : ‖embed u‖≤‖embed v‖) (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2) : normal u v≠0 := by
  have hupos : 0<‖embed u‖ := norm_pos_iff.mpr hu
  have hip2 : ⟪embed u,embed v⟫^2≤‖embed u‖^4/4 := by
    have hh := mul_self_le_mul_self (abs_nonneg ⟪embed u,embed v⟫) hip
    nlinarith [sq_abs ⟪embed u,embed v⟫]
  have huv2 := pow_le_pow_left₀ (norm_nonneg _) huv 2
  have hprod := mul_le_mul_of_nonneg_left huv2 (sq_nonneg ‖embed u‖)
  have hGram : 0<‖embed u‖^2*‖embed v‖^2-⟪embed u,embed v⟫^2 := by
    nlinarith [sq_pos_of_pos hupos,sq_pos_of_pos (sq_pos_of_pos hupos)]
  intro hz
  have he := normal_length u v
  have her : (dot (normal u v) (normal u v):ℝ)=
      (dot u u:ℝ)*(dot v v:ℝ)-(dot u v:ℝ)^2 := by exact_mod_cast he
  rw [hz] at her
  have hzero : (dot (0 : Vector ℤ) 0:ℝ)=0 := by simp [dot]
  rw [hzero] at her
  have huu := inner_embed u u
  have hvv := inner_embed v v
  have huv' := inner_embed u v
  rw [real_inner_self_eq_norm_sq] at huu hvv
  nlinarith

@[expose] def coefficientA (u v z : Vector ℤ) : ℝ :=
  ((dot u z:ℝ)*(dot v v:ℝ)-(dot v z:ℝ)*(dot u v:ℝ))/(dot (normal u v) (normal u v):ℝ)
@[expose] def coefficientB (u v z : Vector ℤ) : ℝ :=
  ((dot v z:ℝ)*(dot u u:ℝ)-(dot u z:ℝ)*(dot u v:ℝ))/(dot (normal u v) (normal u v):ℝ)
@[expose] def normalComponent (u v z : Vector ℤ) : E :=
  ((dot (normal u v) z:ℝ)/(dot (normal u v) (normal u v):ℝ)) • embed (normal u v)

/-- Explicit actual orthogonal decomposition with the ORIGINAL integer
cross product. The coefficients are constructed, not supplied by a
projection-existence hypothesis. -/
theorem actual_decomposition (u v z : Vector ℤ) (hn : normal u v≠0) :
    embed z=coefficientA u v z • embed u+coefficientB u v z • embed v+normalComponent u v z := by
  have hd : (dot (normal u v) (normal u v):ℝ)≠0 := by
    exact_mod_cast (ne_of_gt (dot_self_positive _ hn))
  ext i
  fin_cases i <;>
    simp [embed,coefficientA,coefficientB,normalComponent] <;>
    field_simp [hd] <;>
    simp only [dot,normal,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow] <;> ring

lemma normal_orthogonal (u v z : Vector ℤ) :
    ⟪embed u,normalComponent u v z⟫=0 ∧ ⟪embed v,normalComponent u v z⟫=0 := by
  have hu : dot u (normal u v)=0 := by rw [dot_comm,normal_dot_left]
  have hv : dot v (normal u v)=0 := by rw [dot_comm,normal_dot_right]
  constructor <;> simp only [normalComponent,real_inner_smul_right,inner_embed,hu,hv,Int.cast_zero,mul_zero]

/-- Exact squared normal height of the actual original point. -/
lemma normal_component_norm_sq (u v z : Vector ℤ) (hn : normal u v≠0) :
    ‖normalComponent u v z‖^2=
      (dot (normal u v) z:ℝ)^2/(dot (normal u v) (normal u v):ℝ) := by
  have hd : (dot (normal u v) (normal u v):ℝ)≠0 := by
    exact_mod_cast (ne_of_gt (dot_self_positive _ hn))
  rw [←real_inner_self_eq_norm_sq]
  simp only [normalComponent,real_inner_smul_left,real_inner_smul_right,inner_embed]
  field_simp [hd] <;> ring

end OriginalIntegerNormalProjection318
