module
public import PELOriginalSiegelNormalization318
public section
noncomputable section
namespace PELOriginalSiegelCoercivity318
open PELQuaternionRealRepresentation318 PELOriginalSiegelMatrix318
variable (τ:ℂ) (hτ:0<τ.im)
@[expose] def coercive:ℝ:=alpha*τ.im/5*min 1 (1/Complex.normSq τ)
lemma normSq_positive (hτ:0<τ.im):0<Complex.normSq τ:=
  Complex.normSq_pos.mpr (PELOriginalSiegelNormalization318.parameter_ne τ hτ)
lemma coercive_positive (hτ:0<τ.im):0<coercive τ:=
  mul_pos (div_pos (mul_pos alpha_pos hτ) (by norm_num))
    (lt_min (by norm_num) (one_div_pos.mpr (normSq_positive τ hτ)))
lemma sum_squares_identity (x:Fin 2→ℝ):
    ((beta+1)*x 0-2*x 1)^2+((beta-1)*x 0+2*x 1)^2-
      4*((x 0)^2+(x 1)^2)=4*((x 0)^2+(x 0-x 1)^2):=by
  ring_nf
  simp only [beta_sq]
  ring
/-- A constructed strictly positive Gaussian coercivity constant for the
ACTUAL normalized period matrix, valid for every real vector. -/
lemma energy_lower (hτ:0<τ.im) (x:Fin 2→ℝ):coercive τ*((x 0)^2+(x 1)^2)≤energy τ x:=by
  let m:=min 1 (1/Complex.normSq τ)
  have hm:0≤m:=(lt_min (by norm_num) (one_div_pos.mpr (normSq_positive τ hτ))).le
  let U:=((beta+1)*x 0-2*x 1)^2
  let V:=((beta-1)*x 0+2*x 1)^2
  have hU:0≤U:=sq_nonneg _
  have hV:0≤V:=sq_nonneg _
  have hsum:4*((x 0)^2+(x 1)^2)≤U+V:=by
    have h:=sum_squares_identity x
    have hp:=sq_nonneg (x 0-x 1)
    have hp0:=sq_nonneg (x 0)
    dsimp [U,V]
    nlinarith
  have hsmall:m*(U+V)≤U+V/Complex.normSq τ:=by
    have h1:=mul_le_mul_of_nonneg_right (min_le_left 1 (1/Complex.normSq τ)) hU
    have h2:=mul_le_mul_of_nonneg_right (min_le_right 1 (1/Complex.normSq τ)) hV
    calc
      m*(U+V)=m*U+m*V:=mul_add _ _ _
      _≤1*U+(1/Complex.normSq τ)*V:=add_le_add h1 h2
      _=U+V/Complex.normSq τ:=by ring
  have hall:=le_trans (mul_le_mul_of_nonneg_left hsum hm) hsmall
  have hpos:0≤alpha*τ.im/20:=
    (div_pos (mul_pos alpha_pos hτ) (by norm_num : (0:ℝ)<20)).le
  have h:=mul_le_mul_of_nonneg_left hall hpos
  rw [energy_squares]
  dsimp [coercive,m,U,V] at *
  nlinarith
end PELOriginalSiegelCoercivity318
