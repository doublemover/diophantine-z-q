module
public import ActualGaussianWeberQuarterTurn318
public section
noncomputable section

namespace ActualGaussianWeberQuarterTurnAdd318

open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuarterTurn318

variable {K : Type*} [Field K] [DecidableEq K]

private theorem negY0 (x y : K) : WeierstrassCurve.Affine.negY ((curve K).toAffine) x y= -y := by
  simp [negY,curve,toAffine]

private theorem addX0 (x z s : K) : WeierstrassCurve.Affine.addX ((curve K).toAffine) x z s=s^2-x-z := by
  simp [addX,curve,toAffine]

private theorem addY0 (x z y s : K) : WeierstrassCurve.Affine.addY ((curve K).toAffine) x z y s= -(s*(WeierstrassCurve.Affine.addX ((curve K).toAffine) x z s-x)+y) := by
  rw [addY,negY0,negAddY]

private theorem inv_turn_factor (i : K) (hi : i^2 = -1) : (-i)*i=1 := by
  linear_combination -hi

private theorem turn_ne_zero (i : K) (hi : i^2 = -1) : i≠0 := by
  intro h
  have e := inv_turn_factor i hi
  rw [h,mul_zero] at e
  exact zero_ne_one e

private theorem ratio_of_turn (i : K) (hi : i^2 = -1) (N D : K) :
    N/(i*D)=(-i)*(N/D) := by
  by_cases hD : D=0
  · simp [hD]
  · symm
    apply (eq_div_iff (mul_ne_zero (turn_ne_zero i hi) hD)).2
    calc
      (-i)*(N/D)*(i*D) = ((-i)*i)*(N/D*D) := by ring
      _ = N := by rw [inv_turn_factor i hi,one_mul,div_mul_cancel₀ _ hD]

private theorem stock_slope_turn (i : K) (hi : i^2 = -1) {a b c d : K}
    (hO : ¬(a=c ∧ b=WeierstrassCurve.Affine.negY ((curve K).toAffine) c d))
    (hT : ¬(-a= -c ∧ i*b=WeierstrassCurve.Affine.negY ((curve K).toAffine) (-c) (i*d))) :
    WeierstrassCurve.Affine.slope ((curve K).toAffine) (-a) (-c) (i*b) (i*d)=(-i)*WeierstrassCurve.Affine.slope ((curve K).toAffine) a c b d := by
  by_cases hx : a=c
  · have hxt : -a= -c := congrArg Neg.neg hx
    rw [slope_of_Y_ne hxt (fun h => hT ⟨hxt,h⟩),slope_of_Y_ne hx (fun h => hO ⟨hx,h⟩)]
    simp only [negY,curve,toAffine,mul_zero,zero_mul,add_zero,sub_zero]
    rw [show (-a)^2=a^2 by ring,
        show i*b - -(i*b)=i*(b - -b) by ring]
    exact ratio_of_turn i hi _ _
  · have hxt : -a≠ -c := fun h => hx (neg_injective h)
    rw [slope_of_X_ne hxt,slope_of_X_ne hx]
    rw [show i*b-i*d=i*(b-d) by ring,show -a - -c= -(a-c) by ring]
    rw [div_neg,mul_div_assoc,neg_mul]

private theorem stock_X_turn (i : K) (hi : i^2 = -1) (a c s : K) :
    WeierstrassCurve.Affine.addX ((curve K).toAffine) (-a) (-c) ((-i)*s)= -WeierstrassCurve.Affine.addX ((curve K).toAffine) a c s := by
  rw [addX0,addX0]
  linear_combination s^2 * hi

private theorem stock_Y_turn (i : K) (hi : i^2 = -1) (a c b s : K) :
    WeierstrassCurve.Affine.addY ((curve K).toAffine) (-a) (-c) (i*b) ((-i)*s)=i*WeierstrassCurve.Affine.addY ((curve K).toAffine) a c b s := by
  rw [addY0,addY0,stock_X_turn i hi]
  ring

/-- True addition for the explicit coordinate quarter turn. Both
stock tangent/secant branches scale the slope by −i; inverse points
remain inverse, including finite 2-torsion. -/
theorem turn_add (h2 : (2:K) ≠ 0) (i : K) (hi : i^2 = -1) (P Q : WP K) :
    turn h2 i hi (P+Q)=turn h2 i hi P+turn h2 i hi Q := by
  cases P with
  | zero =>
    change turn h2 i hi (0+Q)=0+turn h2 i hi Q
    simp only [zero_add]
  | some a b hP =>
    cases Q with
    | zero =>
      change turn h2 i hi (Point.some a b hP+0)=turn h2 i hi (Point.some a b hP)+0
      simp only [add_zero]
    | some c d hQ =>
      have hO : (a=c ∧ b=WeierstrassCurve.Affine.negY ((curve K).toAffine) c d) ↔
          (-a= -c ∧ i*b=WeierstrassCurve.Affine.negY ((curve K).toAffine) (-c) (i*d)) := by
        simp only [negY0]
        constructor
        · rintro ⟨hx,hy⟩
          exact ⟨congrArg Neg.neg hx,by rw [hy,mul_neg]⟩
        · rintro ⟨hx,hy⟩
          apply And.intro (neg_injective hx)
          apply mul_left_cancel₀ (turn_ne_zero i hi)
          simpa only [mul_neg] using hy
      by_cases h : a=c ∧ b=WeierstrassCurve.Affine.negY ((curve K).toAffine) c d
      · have ht := hO.mp h
        rw [Point.add_of_Y_eq h.1 h.2, turn_some, turn_some,
            Point.add_of_Y_eq ht.1 ht.2] <;> rfl
      · have ht := fun h' => h (hO.mpr h')
        rw [Point.add_some h,turn_some,turn_some,turn_some,Point.add_some ht]
        have hS := stock_slope_turn i hi h ht
        apply some_transport
        · rw [hS,stock_X_turn i hi]
        · rw [hS,stock_Y_turn i hi]

theorem turn_sq (h2 : (2:K) ≠ 0) (i : K) (hi : i^2 = -1) (P : WP K) :
    turn h2 i hi (turn h2 i hi P)= -P := by
  cases P with
  | zero => rfl
  | some a b h =>
    rw [turn_some,turn_some,Point.neg_some]
    refine some_transport (neg_neg _) ?_
    rw [negY0]
    linear_combination b * hi

@[expose] def turnHom (h2 : (2:K) ≠ 0) (i : K) (hi : i^2 = -1) : WP K →+ WP K where
  toFun := turn h2 i hi
  map_zero' := rfl
  map_add' := turn_add h2 i hi

end ActualGaussianWeberQuarterTurnAdd318
