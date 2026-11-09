module
public import RealGuardTrace318
public section
noncomputable section
namespace CoherentMultipleCharts318
open ConcreteG8Domain (K D)
open LocalGenerator318 (E P)
open GlobalGeneratorPoints318 (R double_R)
open CompressedGeneratorBridge318 (transport curve_eq transport_some)
open WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

lemma D_eq : CompressedOrientation318.D=D := by
  ext <;> norm_num [CompressedOrientation318.D,ConcreteG8Domain.D,ConcreteG8Domain.i,ConcreteG8Domain.pair,pow_succ]

lemma denominator_ne (x : K) : x^2+D≠0 := by
  intro he
  have hr := congrArg ActualQuadraticEmbeddings318.positiveEmbedding he
  simp only [map_add,map_pow,map_zero] at hr
  have hd := RealMultiples318.real_D_gt_one ActualQuadraticEmbeddings318.positiveEmbedding
  nlinarith [sq_nonneg (ActualQuadraticEmbeddings318.positiveEmbedding x)]

/-- The historical rational duplication chart, not a square root chosen
independently at each integer. Its argument is the half point T. -/
@[expose] def u : E.Point → K
  | .zero => 0
  | .some x y _ => 2*y/(x^2+D)
@[expose] def v : E.Point → K
  | .zero => 1
  | .some x _ _ => (x^4-6*D*x^2+D^2)/(x^2+D)^2

theorem curve (Q : E.Point) : (v Q)^2=1-CompressedOrientation318.D*(u Q)^4 := by
  cases Q with
  | zero => simp [u,v]
  | some x y h =>
    have hc : y^2=x^3-D*x := by
      simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1
    rw [D_eq]
    dsimp [u,v]
    field_simp [denominator_ne x]
    linear_combination 16*D*(y^2+x^3-D*x)*hc

/-- Exact oriented doubling with every identity/two-torsion branch retained. -/
theorem point (Q : E.Point) :
    transport curve_eq (PrimaryFormal318.point (u Q) (v Q)
      (ReciprocalDifference318.ordinate_ne _ _ (curve Q)) (curve Q))=Q+Q := by
  cases Q with
  | zero =>
    change _=(0:E.Point)+(0:E.Point)
    simp [u,PrimaryFormal318.point]
  | some x y h =>
    by_cases hy : y=0
    · have he : Point.some x y h+Point.some x y h=0 :=
        Point.add_self_of_Y_eq (by simp [negY,E,hy])
      rw [he]
      simp [u,hy,PrimaryFormal318.point]
    have hneg : y≠E.negY x y := by
      simp only [negY,E,zero_mul,sub_zero]
      intro he
      exact (mul_ne_zero (by norm_num : (2:K)≠0) hy) (by linear_combination he)
    have hu : u (Point.some x y h)≠0 :=
      div_ne_zero (mul_ne_zero (by norm_num) hy) (denominator_ne x)
    have hx : E.addX x x (E.slope x x y y)=1/(u (Point.some x y h))^2 := by
      rw [ValuationDuplication318.actual_doubling_x x y h hy]
      dsimp [u]
      field_simp [hy,denominator_ne x]
    have hs : E.slope x x y y=(3*x^2-D)/(2*y) := by
      rw [slope_of_Y_ne rfl hneg]
      simp only [E,zero_mul,sub_zero,negY,sub_neg_eq_add]
      congr 1 <;> ring
    have hc : y^2=x^3-D*x := by
      simpa only [equation_iff,E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using h.1
    have hv : v (Point.some x y h)/(u (Point.some x y h))^3=
        E.addY x x y (E.slope x x y y) := by
      rw [addY,negAddY,negY,hx,hs]
      simp only [E,zero_mul,sub_zero]
      dsimp [u,v]
      field_simp [hy,denominator_ne x]
      linear_combination -(4*D*x+4*x^3-8*y^2)*hc
    rw [PrimaryFormal318.point,dite_eq_right hu,transport_some,Point.add_self_of_Y_ne hneg,
      Point.some.injEq]
    exact ⟨hx.symm,hv⟩

@[expose] def chartU (n : ℤ) : K := u (n • R)
@[expose] def chartV (n : ℤ) : K := v (n • R)

theorem chart_curve (n : ℤ) :
    (chartV n)^2=1-CompressedOrientation318.D*(chartU n)^4 := curve _

theorem chart_point (n : ℤ) :
    transport curve_eq (PrimaryFormal318.point (chartU n) (chartV n)
      (ReciprocalDifference318.ordinate_ne _ _ (chart_curve n)) (chart_curve n))=n • P := by
  rw [←double_R,zsmul_add]
  exact point (n • R)

@[simp] theorem u_zero : u 0=0 := rfl
@[simp] theorem v_zero : v 0=1 := rfl

theorem u_negative (Q : E.Point) : u (-Q)= -u Q := by
  cases Q with
  | zero =>
    change u (-(0:E.Point))= -u 0
    simp
  | some x y h =>
    rw [Point.neg_some h]
    simp [u,negY,E]
    ring

theorem v_negative (Q : E.Point) : v (-Q)=v Q := by
  cases Q with
  | zero =>
    change v (-(0:E.Point))=v 0
    simp
  | some x y h =>
    rw [Point.neg_some h]
    rfl

@[simp] theorem chartU_zero : chartU 0=0 := by simp [chartU]
@[simp] theorem chartV_zero : chartV 0=1 := by simp [chartV]
@[simp] theorem chartU_negative (n : ℤ) : chartU (-n)= -chartU n := by
  simp only [chartU,neg_zsmul,u_negative]
@[simp] theorem chartV_negative (n : ℤ) : chartV (-n)=chartV n := by
  simp only [chartV,neg_zsmul,v_negative]

theorem chartU_zero_iff (n : ℤ) : chartU n=0 ↔ n=0 := by
  constructor
  · intro hu
    have hp := chart_point n
    simp [PrimaryFormal318.point,hu] at hp
    by_contra hn
    exact RealMultiples318.multiple_P_nonzero n hn hp.symm
  · intro hn
    subst n
    exact chartU_zero

theorem chart_abscissa (n : ℤ) (hn : n≠0) :
    (n • P).xRep 0=1/(chartU n)^2 := by
  have hu : chartU n≠0 := fun he => hn ((chartU_zero_iff n).mp he)
  rw [←chart_point n,PrimaryFormal318.point,dite_eq_right hu,transport_some]
  simp only [Point.xRep_some,Matrix.cons_val_zero]

/-- The historically prescribed signed root candidate, fixed before h. -/
@[expose] def fixedRoot (n : ℤ) : K := -(1/chartU n)

theorem fixedRoot_square (n : ℤ) (hn : n≠0) :
    (fixedRoot n)^2=(n • P).xRep 0 := by
  rw [chart_abscissa n hn]
  simp [fixedRoot]

theorem fixedRoot_ne_zero (n : ℤ) (hn : n≠0) : fixedRoot n≠0 := by
  exact neg_ne_zero.mpr (one_div_ne_zero (fun he => hn ((chartU_zero_iff n).mp he)))

end CoherentMultipleCharts318
