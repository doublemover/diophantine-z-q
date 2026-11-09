module
public import RealGuardTrace318
public section
noncomputable section
namespace ActualMultipleCharts318
open ConcreteG8Domain (K)
open LocalGenerator318 (E P)
open GlobalGeneratorPoints318 (R double_R)
open CompressedGeneratorBridge318 (transport curve_eq transport_some)
open WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

lemma D_eq : CompressedOrientation318.D=ConcreteG8Domain.D := by
  ext <;> norm_num [CompressedOrientation318.D,ConcreteG8Domain.D,ConcreteG8Domain.i,ConcreteG8Domain.pair,pow_succ]

/-- The exact source chart, interpreted in the actual global curve group. -/
@[expose] def Chart (Q : E.Point) : Prop := ∃ u v : K,
  ∃ hc : v^2=1-CompressedOrientation318.D*u^4,
    transport curve_eq (PrimaryFormal318.point u v
      (ReciprocalDifference318.ordinate_ne u v hc) hc)=Q

lemma chart_zero : Chart 0 := by
  refine ⟨0,1,by ring,?_⟩
  simp [PrimaryFormal318.point]

/-- Every double in the actual K-point group admits an oriented source chart,
including all identity and two-torsion input branches. -/
theorem chart_double (Q : E.Point) : Chart (Q+Q) := by
  by_cases hz : Q+Q=0
  · rw [hz]
    exact chart_zero
  cases Q with
  | zero => exact False.elim (hz (zero_add 0))
  | some x y h =>
    have hy : y≠0 := by
      intro he
      subst y
      apply hz
      apply Point.add_self_of_Y_eq
      simp [negY,E]
    have hneg : y≠E.negY x y := by
      simp only [negY,E,zero_mul,sub_zero]
      intro he
      exact (mul_ne_zero (by norm_num : (2:K)≠0) hy) (by linear_combination he)
    have hq : x^2+ConcreteG8Domain.D≠0 := by
      intro he
      have hr := congrArg ActualQuadraticEmbeddings318.positiveEmbedding he
      simp only [map_add,map_pow,map_zero] at hr
      have hd := RealMultiples318.real_D_gt_one ActualQuadraticEmbeddings318.positiveEmbedding
      nlinarith [sq_nonneg (ActualQuadraticEmbeddings318.positiveEmbedding x)]
    let u : K := 2*y/(x^2+ConcreteG8Domain.D)
    let v : K := E.addY x x y (E.slope x x y y)*u^3
    have hu : u≠0 := div_ne_zero (mul_ne_zero (by norm_num) hy) hq
    have hx : E.addX x x (E.slope x x y y)=1/u^2 := by
      rw [ValuationDuplication318.actual_doubling_x x y h hy]
      dsimp [u]
      field_simp [hy,hq]
    have hn := nonsingular_add h h (fun he => hneg he.2)
    have hc0 : (E.addY x x y (E.slope x x y y))^2=
        (1/u^2)^3-ConcreteG8Domain.D*(1/u^2) := by
      have he := hn.1
      rw [equation_iff,hx] at he
      simpa only [E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using he
    have hc : v^2=1-CompressedOrientation318.D*u^4 := by
      rw [D_eq]
      dsimp [v]
      field_simp [hu] at hc0 ⊢
      linear_combination hc0
    refine ⟨u,v,hc,?_⟩
    rw [PrimaryFormal318.point,dite_eq_right hu,transport_some,Point.add_self_of_Y_ne hneg]
    rw [Point.some.injEq]
    constructor
    · exact hx.symm
    · dsimp [v]
      field_simp [hu]

/-- Every integer multiple of the fixed actual generator has a chart, with
no assumed square roots or point-sign choices. -/
theorem chart_multiple (n : ℤ) : Chart (n • P) := by
  rw [←double_R,zsmul_add]
  exact chart_double (n • R)

/-- Canonically chosen from the proved source-chart existence; no extra
point or square-root existence assumption is introduced. -/
@[expose] def chartU (n : ℤ) : K := Classical.choose (chart_multiple n)
@[expose] def chartV (n : ℤ) : K := (Classical.choose_spec (chart_multiple n)).choose

theorem chart_curve (n : ℤ) :
    (chartV n)^2=1-CompressedOrientation318.D*(chartU n)^4 :=
  (Classical.choose_spec (chart_multiple n)).choose_spec.choose

theorem chart_point (n : ℤ) :
    transport curve_eq (PrimaryFormal318.point (chartU n) (chartV n)
      (ReciprocalDifference318.ordinate_ne _ _ (chart_curve n)) (chart_curve n))=n • P :=
  (Classical.choose_spec (chart_multiple n)).choose_spec.choose_spec

theorem chartU_zero_iff (n : ℤ) : chartU n=0 ↔ n=0 := by
  constructor
  · intro hu
    have hp := chart_point n
    simp [PrimaryFormal318.point,hu] at hp
    by_contra hn
    exact RealMultiples318.multiple_P_nonzero n hn hp.symm
  · intro hn
    subst n
    have hp := chart_point 0
    have hz : PrimaryFormal318.point (chartU 0) (chartV 0)
        (ReciprocalDifference318.ordinate_ne _ _ (chart_curve 0)) (chart_curve 0)=0 := by
      apply (transport curve_eq).injective
      simpa using hp
    exact (PrimaryFormal318.point_zero_iff _ _ _ _).mp hz

end ActualMultipleCharts318
