module
public import OriginalFullDualLattice318
public section
noncomputable section
namespace OriginalIntegerSquaredNorm318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralIntegerDuality318 OriginalEuclideanLattice318
set_option maxHeartbeats 2500000

lemma dot_self_nonneg (v : Vector ℤ) : 0≤dot v v := by
  dsimp [dot]
  nlinarith [sq_nonneg v.1,sq_nonneg v.2.1,sq_nonneg v.2.2]

/-- Exact squared Euclidean length of the original integer numerator,
encoded as a natural number so actual minima can be constructed. -/
@[expose] def squaredLength (v : Vector ℤ) : ℕ := (dot v v).toNat

lemma norm_sq (v : Vector ℤ) : ‖embed v‖^2=(squaredLength v:ℝ) := by
  have he : (squaredLength v:ℤ)=dot v v := Int.toNat_of_nonneg (dot_self_nonneg v)
  rw [←real_inner_self_eq_norm_sq,inner_embed,←he]
  simp only [Int.cast_natCast]

lemma squaredLength_zero_iff (v : Vector ℤ) : squaredLength v=0 ↔ v=0 := by
  constructor
  · intro hv
    have hh := norm_sq v
    rw [hv,Nat.cast_zero] at hh
    have he : embed v=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (embed v)])
    apply embed_injective
    rwa [embed_zero]
  · intro hv
    subst v
    simp [squaredLength,dot]

lemma length_le_norm_iff (v u : Vector ℤ) :
    squaredLength v≤squaredLength u ↔ ‖embed v‖≤‖embed u‖ := by
  have hv := norm_sq v
  have hu := norm_sq u
  constructor
  · intro h
    have hh : (squaredLength v:ℝ)≤(squaredLength u:ℝ) := by exact_mod_cast h
    nlinarith [norm_nonneg (embed v),norm_nonneg (embed u)]
  · intro h
    have hh : (squaredLength v:ℝ)≤(squaredLength u:ℝ) := by
      nlinarith [norm_nonneg (embed v),norm_nonneg (embed u)]
    exact_mod_cast hh

@[expose] def axis (i : Fin 3) : Vector ℤ :=
  (if i=0 then 1 else 0,if i=1 then 1 else 0,if i=2 then 1 else 0)

lemma embed_axis (i : Fin 3) : embed (axis i)=EuclideanSpace.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [axis,embed,EuclideanSpace.single,PiLp.single_apply]

lemma axes_independent : LinearIndependent ℝ (fun i : Fin 3 => embed (axis i)) := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).linearIndependent
  simpa only [EuclideanSpace.basisFun_apply,embed_axis] using h

@[expose] def multipleAxis (M : ℕ) (i : Fin 3) : Vector ℤ :=
  ((M:ℤ)*(axis i).1,(M:ℤ)*(axis i).2.1,(M:ℤ)*(axis i).2.2)

lemma embed_multipleAxis (M : ℕ) (i : Fin 3) :
    embed (multipleAxis M i)=(M:ℝ) • embed (axis i) := by
  ext j
  fin_cases j <;> simp [embed,multipleAxis]

lemma multiple_axes_independent (M : ℕ) (hM : 0<M) :
    LinearIndependent ℝ (fun i : Fin 3 => embed (multipleAxis M i)) := by
  have hm : (M:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have h := axes_independent.units_smul (fun _ => Units.mk0 (M:ℝ) hm)
  simpa only [Pi.smul_apply,Pi.smul_apply',Units.smul_def,Units.val_mk0,embed_multipleAxis] using h

@[expose] def tripleScore (v : Fin 3 → Vector ℤ) : ℕ :=
  max (squaredLength (v 0)) (max (squaredLength (v 1)) (squaredLength (v 2)))

lemma length_le_score (v : Fin 3 → Vector ℤ) (i : Fin 3) : squaredLength (v i)≤tripleScore v := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

lemma score_bound (v : Fin 3 → Vector ℤ) (r : ℝ) (hr : 0≤r)
    (hv : ∀ i, ‖embed (v i)‖≤r) : (tripleScore v:ℝ)≤r^2 := by
  have h (i : Fin 3) : (squaredLength (v i):ℝ)≤r^2 := by
    rw [←norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hv i) 2
  simpa only [tripleScore,Nat.cast_max] using max_le (h 0) (max_le (h 1) (h 2))

lemma norm_le_sqrt_score (v : Fin 3 → Vector ℤ) (i : Fin 3) :
    ‖embed (v i)‖≤Real.sqrt (tripleScore v:ℝ) := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤tripleScore v by positivity)
  have hle : (squaredLength (v i):ℝ)≤(tripleScore v:ℝ) := by exact_mod_cast length_le_score v i
  have hn := norm_sq (v i)
  nlinarith [norm_nonneg (embed (v i)),Real.sqrt_nonneg (tripleScore v:ℝ)]

end OriginalIntegerSquaredNorm318
