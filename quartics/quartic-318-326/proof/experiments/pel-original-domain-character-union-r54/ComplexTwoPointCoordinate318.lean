module
public import PELOriginalBranchLabels318
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public section
noncomputable section
namespace ComplexTwoPointCoordinate318
set_option maxHeartbeats 1500000

@[expose] def coordinate (a b z : ℂ) : ℂ := (z-a)/(z-b)
@[expose] def inverse (a b w : ℂ) : ℂ := (b*w-a)/(w-1)

theorem coordinate_ne_one (a b : ℂ) (hab : a≠b) (z : ℂ) (hz : z≠b) :
    coordinate a b z≠1 := by
  intro he
  have h := (div_eq_iff (sub_ne_zero.mpr hz)).mp he
  have heq : a=b := by linear_combination -h
  exact hab heq

theorem inverse_ne_second (a b : ℂ) (hab : a≠b) (w : ℂ) (hw : w≠1) :
    inverse a b w≠b := by
  intro he
  have h := (div_eq_iff (sub_ne_zero.mpr hw)).mp he
  have heq : a=b := by linear_combination -h
  exact hab heq

theorem inverse_coordinate (a b : ℂ) (hab : a≠b) (z : ℂ) (hz : z≠b) :
    inverse a b (coordinate a b z)=z := by
  unfold inverse coordinate
  field_simp [sub_ne_zero.mpr hz,sub_ne_zero.mpr hab] <;> ring

theorem coordinate_inverse (a b : ℂ) (hab : a≠b) (w : ℂ) (hw : w≠1) :
    coordinate a b (inverse a b w)=w := by
  unfold inverse coordinate
  field_simp [sub_ne_zero.mpr hw,sub_ne_zero.mpr hab] <;> ring

/-- A literal complex coordinate with explicit inverse and full open
domain/target, rather than a formal power series or assumed local parameter. -/
@[expose] def chart (a b : ℂ) (hab : a≠b) : OpenPartialHomeomorph ℂ ℂ where
  toFun := coordinate a b
  invFun := inverse a b
  source := {z | z≠b}
  target := {w | w≠1}
  map_source' := coordinate_ne_one a b hab
  map_target' := inverse_ne_second a b hab
  left_inv' := inverse_coordinate a b hab
  right_inv' := coordinate_inverse a b hab
  open_source := isOpen_ne continuous_id continuous_const
  open_target := isOpen_ne continuous_id continuous_const
  continuousOn_toFun := (continuousOn_id.sub continuousOn_const).div
    (continuousOn_id.sub continuousOn_const) (fun _ hz => sub_ne_zero.mpr hz)
  continuousOn_invFun := ((continuousOn_const.mul continuousOn_id).sub continuousOn_const).div
    (continuousOn_id.sub continuousOn_const) (fun _ hw => sub_ne_zero.mpr hw)

theorem coordinate_analytic (a b z : ℂ) (hz : z≠b) : AnalyticAt ℂ (coordinate a b) z :=
  (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz)

theorem inverse_analytic (a b w : ℂ) (hw : w≠1) : AnalyticAt ℂ (inverse a b) w :=
  ((analyticAt_const.mul analyticAt_id).sub analyticAt_const).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hw)

theorem coordinate_center (a b : ℂ) : coordinate a b a=0 := by simp [coordinate]
theorem inverse_center (a b : ℂ) : inverse a b 0=a := by simp [inverse]

theorem coordinate_derivative (a b : ℂ) (hab : a≠b) :
    HasDerivAt (coordinate a b) ((a-b)⁻¹) a := by
  have h := PELInertiaArithmeticFixedPoints318.fractional_derivative
    (1:ℂ) (-a) 1 (-b) a (by simpa using sub_ne_zero.mpr hab)
  have he : (1*(-b)-(-a)*1)/(1*a+(-b))^2=(a-b)⁻¹ := by
    field_simp [sub_ne_zero.mpr hab] <;> ring
  rw [he] at h
  simpa only [one_mul,add_neg_eq_sub,coordinate] using h
end ComplexTwoPointCoordinate318
