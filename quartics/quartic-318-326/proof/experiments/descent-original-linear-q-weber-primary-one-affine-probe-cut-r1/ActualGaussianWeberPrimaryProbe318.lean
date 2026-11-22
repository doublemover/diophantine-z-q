module
public import ActualGaussianWeberOrdinarySlope318
public section
noncomputable section

namespace ActualGaussianWeberPrimaryProbe318

open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberOrdinarySlope318

variable {K : Type*} [Field K] [DecidableEq K]

private theorem transport {x y z w : K}
    {h : (curve K).toAffine.Nonsingular x y} {j : (curve K).toAffine.Nonsingular z w}
    (hx : x=z) (hy : y=w) : Point.some x y h=Point.some z w j := by
  subst z
  subst w
  rfl

theorem i_ne_zero (i : K) (hi : i^2= -1) : i≠0 := by
  intro H
  rw [H,zero_pow (by decide : (2:ℕ)≠0)] at hi
  exact (neg_ne_zero.mpr one_ne_zero) hi.symm

theorem probe_y_ne (h2 : (2:K)≠0) (i : K) (hi : i^2= -1) : 1-i≠0 := by
  intro H
  have h : i=1 := (sub_eq_zero.mp H).symm
  have e : (2:K)=0 := by
    rw [h,one_pow] at hi
    linear_combination hi
  exact h2 e

theorem probe_equation (i : K) (hi : i^2= -1) : (1-i)^2=i^3-i := by
  linear_combination (1-i)*hi

@[expose] def probe (h2 : (2:K)≠0) (i : K) (hi : i^2= -1) : WP K :=
  Point.some i (1-i) (nonsing_of_equation h2 (probe_equation i hi))

@[expose] def twoPoint (h2 : (2:K)≠0) : WP K :=
  Point.some 0 0 (nonsing_of_equation h2 (by ring))

theorem twoPoint_double (h2 : (2:K)≠0) : twoPoint h2+twoPoint h2=0 := by
  unfold twoPoint
  exact Point.add_of_Y_eq rfl (by rw [literal_negY,neg_zero])

/-- The actual rational point Q=(i,1−i) has double exactly the nonzero
T₀=(0,0). Both coordinates are computed using the stock tangent branch. -/
theorem probe_double (h2 : (2:K)≠0) (i : K) (hi : i^2= -1) :
    probe h2 i hi+probe h2 i hi=twoPoint h2 := by
  let y := 1-i
  let e := (curve K).toAffine
  have hy0 : y≠0 := probe_y_ne h2 i hi
  have hy : y≠ -y := by
    intro H
    have h : (2:K)*y=0 := by linear_combination H
    exact mul_ne_zero h2 hy0 h
  have hB : ¬(i=i ∧ y=e.negY i y) := by
    intro H
    apply hy
    simpa only [literal_negY] using H.2
  have hs : e.slope i i y y= -(1+i) := by
    rw [literal_tangent_slope rfl hy]
    apply (div_eq_iff (mul_ne_zero h2 hy0)).mpr
    change 3*i^2-1= -(1+i)*(2*(1-i))
    linear_combination hi
  have hX : e.addX i i (e.slope i i y y)=0 := by
    rw [hs,literal_addX]
    linear_combination hi
  have hY : e.addY i i y (e.slope i i y y)=0 := by
    rw [literal_addY,hX,hs]
    change -((-(1+i))*(0-i)+(1-i))=0
    linear_combination -hi
  unfold probe twoPoint
  rw [Point.add_some hB]
  exact transport hX hY

theorem negative_i_square (i : K) (hi : i^2= -1) : (-i)^2= -1 := by rw [neg_sq,hi]

/-- No full Gaussian action or order computation is required to show
that a primary coefficient pair fixes Q. The displayed integer equalities
are exactly π−1=(1+i)^3(c+di) in the literal Gaussian ring. -/
theorem primary_preserves_probe (h2 : (2:K)≠0) (i : K) (hi : i^2= -1)
    (a b c d : ℤ) (ha : a=1-2*(c+d)) (hb : b=2*(c-d)) :
    a • probe h2 i hi+b • probe h2 (-i) (negative_i_square i hi)=probe h2 i hi := by
  let Q := probe h2 i hi
  let R := probe h2 (-i) (negative_i_square i hi)
  let T := twoPoint (K:=K) h2
  have hQ : (2:ℤ) • Q=T := by rw [two_zsmul,probe_double] <;> rfl
  have hR : (2:ℤ) • R=T := by rw [two_zsmul,probe_double] <;> rfl
  have hT : (2:ℤ) • T=0 := by rw [two_zsmul,twoPoint_double]
  have ha' : a=1+(-(c+d))*2 := by linarith only [ha]
  have hb' : b=(c-d)*2 := by linarith only [hb]
  change a • Q+b • R=Q
  rw [ha',hb',add_zsmul,one_zsmul,mul_zsmul,mul_zsmul,hQ,hR,add_assoc,←add_zsmul]
  rw [show -(c+d)+(c-d)=(-d)*2 by ring,mul_zsmul,hT,smul_zero,add_zero]

/-- The one point distinguishes exactly the four actual unit turns.
When a unit formula fixes Q: the x comparison rules out −x, and the
nonzero y comparison rules out −y. -/
theorem no_other_turn_fixes_probe (h2 : (2:K)≠0) (i : K) (hi : i^2= -1)
    (x y : K) (h : (curve K).toAffine.Nonsingular x y)
    (hQ : Point.some x y h=probe h2 i hi) :
    ¬(x=i ∧ y= -(1-i)) ∧ ¬(x= -i) := by
  have hx : x=i := congrArg (fun P : WP K => match P with | .zero => 0 | .some u _ _ => u) hQ
  have hy : y=1-i := congrArg (fun P : WP K => match P with | .zero => 0 | .some _ v _ => v) hQ
  refine ⟨?_,?_⟩
  · rintro ⟨_,hn⟩
    have e : (2:K)*(1-i)=0 := by linear_combination hn-hy
    exact mul_ne_zero h2 (probe_y_ne h2 i hi) e
  · intro hn
    have e : (2:K)*i=0 := by linear_combination hn-hx
    exact mul_ne_zero h2 (i_ne_zero i hi) e

end ActualGaussianWeberPrimaryProbe318
