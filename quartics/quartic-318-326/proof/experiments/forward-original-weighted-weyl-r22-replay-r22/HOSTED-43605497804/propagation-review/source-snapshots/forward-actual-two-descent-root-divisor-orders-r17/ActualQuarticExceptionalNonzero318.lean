module
public import ActualQuarticRegularNonzero318
public section
noncomputable section
namespace ActualQuarticExceptionalNonzero318
open TernaryQuadraticLineCover318 OriginalAffineSieveEliminants318 ActualAffineQuarticEliminant318
open OriginalCofactorCoordinates318 OriginalIntegerNormalProjection318 LiteralIntegerDuality318
set_option maxHeartbeats 15000000

@[expose] def axisX (κ : ℤ) (a d : Vector ℤ) : ℤ :=
  κ^2*(a.2.2*d.1-a.1*d.2.2)^4+4*d.1^2*(a.2.1*d.1-a.1*d.2.1)^2
@[expose] def axisZ (κ : ℤ) (a d : Vector ℤ) : ℤ :=
  κ^2*(a.2.2*d.2.1-a.2.1*d.2.2)^4+4*d.2.1^2*(a.1*d.2.1-a.2.1*d.1)^2

/-- Exact true quartic factorization at the exceptional ORIGINAL label.
Both factors are the actual K restrictions at the two P'=-2xz roots,
with integer denominator powers cleared, not the old D norm factors. -/
theorem exceptional_factorization (κ : ℤ) (a d : Vector ℤ) :
    actualEliminant κ (-2) a d=
      -128*d.1^3*d.2.1^3*axisX κ a d*axisZ κ a d := by
  simp [actualEliminant,ActualQuadraticQuarticEliminant318.eliminant,
    ActualQuadraticQuarticEliminant318.linearTerm,ActualQuadraticQuarticEliminant318.constantTerm,
    fA,fB,fC,LiteralAdjacentNormSlice318.P',k4,k3,k2,k1,k0,r2,r1,r0,axisX,axisZ]
  ring

lemma x_minors (a v d : Vector ℤ) (hd : determinant a v d≠0) (hdx : d.1≠0) :
    a.2.2*d.1-a.1*d.2.2≠0 ∨ a.2.1*d.1-a.1*d.2.1≠0 := by
  by_contra hn
  push_neg at hn
  have he : d.1*determinant a v d=
      -(a.2.1*d.1-a.1*d.2.1)*(v.1*d.2.2-v.2.2*d.1)+
      (a.2.2*d.1-a.1*d.2.2)*(v.1*d.2.1-v.2.1*d.1) := by
    dsimp [determinant,normal,dot]
    ring
  rw [hn.1,hn.2,neg_zero,zero_mul,zero_mul,zero_add] at he
  exact mul_ne_zero hdx hd he

lemma z_minors (a v d : Vector ℤ) (hd : determinant a v d≠0) (hdz : d.2.1≠0) :
    a.2.2*d.2.1-a.2.1*d.2.2≠0 ∨ a.1*d.2.1-a.2.1*d.1≠0 := by
  by_contra hn
  push_neg at hn
  have he : d.2.1*determinant a v d=
      (a.1*d.2.1-a.2.1*d.1)*(v.2.1*d.2.2-v.2.2*d.2.1)+
      (a.2.2*d.2.1-a.2.1*d.2.2)*(v.1*d.2.1-v.2.1*d.1) := by
    dsimp [determinant,normal,dot]
    ring
  rw [hn.1,hn.2,zero_mul,zero_mul,zero_add] at he
  exact mul_ne_zero hdz hd he

lemma axisX_pos (κ : ℤ) (hκ : κ≠0) (a v d : Vector ℤ)
    (hd : determinant a v d≠0) (hdx : d.1≠0) : 0<axisX κ a d := by
  obtain h|h := x_minors a v d hd hdx
  · have hk := sq_pos_of_ne_zero hκ
    have hm : 0<(a.2.2*d.1-a.1*d.2.2)^4 := pow_pos (sq_pos_of_ne_zero h) 2 |>.trans_eq (by ring)
    dsimp [axisX]
    exact add_pos_of_pos_of_nonneg (mul_pos hk hm) (by positivity)
  · have hm := sq_pos_of_ne_zero h
    have hx := sq_pos_of_ne_zero hdx
    dsimp [axisX]
    exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos (mul_pos (by norm_num) hx) hm)

lemma axisZ_pos (κ : ℤ) (hκ : κ≠0) (a v d : Vector ℤ)
    (hd : determinant a v d≠0) (hdz : d.2.1≠0) : 0<axisZ κ a d := by
  obtain h|h := z_minors a v d hd hdz
  · have hk := sq_pos_of_ne_zero hκ
    have hm : 0<(a.2.2*d.2.1-a.2.1*d.2.2)^4 := pow_pos (sq_pos_of_ne_zero h) 2 |>.trans_eq (by ring)
    dsimp [axisZ]
    exact add_pos_of_pos_of_nonneg (mul_pos hk hm) (by positivity)
  · have hm := sq_pos_of_ne_zero h
    have hz := sq_pos_of_ne_zero hdz
    dsimp [axisZ]
    exact add_pos_of_nonneg_of_pos (by positivity) (mul_pos (mul_pos (by norm_num) hz) hm)

/-- Genuine exceptional eliminant nonvanishing from an actual determinant
and successful original quadratic leading term. No actualK coprimality
or nonvanishing is requested as an input. -/
theorem exceptional_nonzero (κ : ℤ) (hκ : κ≠0) (a v d : Vector ℤ)
    (hd : determinant a v d≠0) (hA : fA true κ (-2) d≠0) :
    actualEliminant κ (-2) a d≠0 := by
  have hdx : d.1≠0 := by intro h;apply hA;simp [fA,h]
  have hdz : d.2.1≠0 := by intro h;apply hA;simp [fA,h]
  rw [exceptional_factorization]
  exact mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hdx)) (pow_ne_zero 3 hdz))
    (axisX_pos κ hκ a v d hd hdx).ne') (axisZ_pos κ hκ a v d hd hdz).ne'

end ActualQuarticExceptionalNonzero318
