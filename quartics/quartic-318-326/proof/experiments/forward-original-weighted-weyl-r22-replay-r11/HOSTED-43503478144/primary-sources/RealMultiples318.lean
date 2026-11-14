module
public import ProductHeight318
public import GlobalHeightPositivity318
public section
noncomputable section
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 GlobalSaturationHeight318
open WeierstrassCurve.Affine ActualCanonicalHeight318
namespace RealMultiples318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

lemma real_D_gt_one (σ:K→+*ℝ) : 1<σ D := by
  have hs : (σ i)^2=(2:ℝ) := by simpa only [map_pow,map_ofNat] using congrArg σ i_square
  have hhi : σ i<2 := by nlinarith
  rw [D,map_pow,map_sub,map_ofNat]
  nlinarith

lemma square_abscissa_gt_one (σ:K→+*ℝ) (r y:K) (hr:r≠0)
    (h:E.Nonsingular (r^2) y) : 1<σ (r^2) := by
  obtain ⟨j,hj,_⟩ := RootPointAlgebra318.factor_of_square_point r y hr h
  have he := congrArg σ hj
  simp only [map_pow,map_sub] at he
  rw [map_pow]
  have hd := real_D_gt_one σ
  have hp := sq_nonneg (σ r)
  have hjp := sq_nonneg (σ j)
  have hq : ((σ r)^2)^2=(σ r)^4 := by ring
  nlinarith

/-- Every finite nonidentity doubled point lies on the x>1 real component
under both real embeddings; identity and all y=0 branches are explicit. -/
lemma double_abscissa_gt_one (σ:K→+*ℝ) (Q:E.Point) (hQ:Q+Q≠0) :
    1<σ ((Q+Q).xRep 0) := by
  cases Q with
  | zero =>
    change (0:E.Point)+(0:E.Point)≠0 at hQ
    exact False.elim (hQ (zero_add 0))
  | some x y h =>
    have hy:y≠0 := by
      intro hz
      subst y
      apply hQ
      apply Point.add_self_of_Y_eq
      simp [negY,E]
    have hneg:y≠E.negY x y := by
      simp only [negY,E,zero_mul,sub_zero]
      intro hh
      have hz:2*y=0 := by linear_combination hh
      exact (mul_ne_zero (by norm_num) hy) hz
    let r:K := (x^2+D)/(2*y)
    have hr:r≠0 := by
      apply div_ne_zero
      · intro hz
        have he := congrArg σ hz
        simp only [map_add,map_pow,map_zero] at he
        nlinarith [real_D_gt_one σ,sq_nonneg (σ x)]
      · exact mul_ne_zero (by norm_num) hy
    have hnew := nonsingular_add h h (fun hh => hneg hh.2)
    have hx : E.addX x x (E.slope x x y y)=r^2 :=
      ValuationDuplication318.actual_doubling_x x y h hy
    have hnew' : E.Nonsingular (r^2) (E.addY x x y (E.slope x x y y)) := by
      rw [←hx]
      exact hnew
    rw [Point.add_self_of_Y_ne hneg]
    simp only [Point.xRep_some,Matrix.cons_val_zero]
    rw [hx]
    exact square_abscissa_gt_one σ r _ hr hnew'

lemma multiple_P_nonzero (n:ℤ) (hn:n≠0) : n • P≠0 := by
  have hR := GlobalHeightPositivity318.canonical_R_positive canonical_data
  have hP : 0<canonicalHeight P := by
    rw [←two_zsmul_R,canonical_data.zsmul]
    positivity
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn
  intro he
  have hh := canonical_data.zsmul n P
  rw [he,canonical_data.zero] at hh
  have hp := mul_pos (sq_pos_of_ne_zero hnR) hP
  linarith

/-- Exact source real-embedding input for every nonzero integer label. -/
theorem multiple_P_abscissa_gt_one (σ:K→+*ℝ) (n:ℤ) (hn:n≠0) :
    1<σ ((n • P).xRep 0) := by
  have he : n • P=(n • R)+(n • R) := by rw [←double_R,zsmul_add]
  have hne := multiple_P_nonzero n hn
  rw [he] at hne ⊢
  exact double_abscissa_gt_one σ (n • R) hne

#print axioms real_D_gt_one
#print axioms square_abscissa_gt_one
#print axioms double_abscissa_gt_one
#print axioms multiple_P_nonzero
#print axioms multiple_P_abscissa_gt_one
end RealMultiples318
