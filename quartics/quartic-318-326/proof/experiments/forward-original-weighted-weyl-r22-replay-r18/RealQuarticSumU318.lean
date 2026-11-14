module
public import RealQuarticAssociativityPolynomial318
public import ReciprocalGroup318
public section
noncomputable section
namespace RealQuarticSumU318
open ReciprocalGroup318
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma denominator_pos {D : ℝ} (hD : 0<D) (u a : ℝ) : 0<1+D*u^2*a^2 := by positivity
lemma denominator_ne {D : ℝ} (hD : 0<D) (u a : ℝ) : 1+D*u^2*a^2≠0 :=
  ne_of_gt (denominator_pos hD u a)

lemma nested_denominator_pos {D : ℝ} (hD : 0<D) (u a p c : ℝ) :
    0<(1+D*u^2*a^2)^2+D*p^2*c^2 := by
  have hp : 0<(1+D*u^2*a^2)^2 := sq_pos_of_pos (denominator_pos hD u a)
  positivity

lemma sumU_left_normalized {D : ℝ} (hD : 0<D) (u v a b c e : ℝ) :
    sumU D (sumU D u v a b) (sumV D u v a b) c e =
    ((u*b+a*v)*e*(1+D*u^2*a^2)+c*(v*b*(1-D*u^2*a^2)-2*D*u*a*(u^2+a^2))) /
      ((1+D*u^2*a^2)^2+D*(u*b+a*v)^2*c^2) := by
  have hq := denominator_ne hD u a
  have hl := ne_of_gt (nested_denominator_pos hD u a (u*b+a*v) c)
  have hs := denominator_ne hD (sumU D u v a b) c
  dsimp [sumU,sumV] at hs ⊢
  field_simp [hq,hl,hs]

lemma sumU_comm (D u v a b : ℝ) : sumU D u v a b=sumU D a b u v := by
  unfold sumU
  congr 1 <;> ring

/-- Global first-coordinate associativity on every real quartic point.
All addition denominators are strictly positive, including every exceptional
identity, inverse, tangent and turning-point branch. -/
theorem sumU_associative {D : ℝ} (hD : 0<D) (u v a b c e : ℝ)
    (hv : v^2=1-D*u^4) (hb : b^2=1-D*a^4) (he : e^2=1-D*c^4) :
    sumU D (sumU D u v a b) (sumV D u v a b) c e =
      sumU D u v (sumU D a b c e) (sumV D a b c e) := by
  rw [sumU_left_normalized hD, sumU_comm D u v (sumU D a b c e) (sumV D a b c e),
    sumU_left_normalized hD]
  have hl := ne_of_gt (nested_denominator_pos hD u a (u*b+a*v) c)
  have hr := ne_of_gt (nested_denominator_pos hD a c (a*e+c*b) u)
  apply (div_eq_div_iff hl hr).mpr
  have hp := RealQuarticAssociativityPolynomial318.cleared_u_associativity D u v a b c e hv hb he
  convert hp using 1
  ring

end RealQuarticSumU318
