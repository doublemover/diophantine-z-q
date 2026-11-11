module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public section
noncomputable section

/-! Explicit rational coordinates for the *literal* level-three j,x quartic.
The comparison with LiteralThreeBaseEvaluation318.Q is made in the separate
consumer. No compactified analytic quotient or algebraic normalization theorem
is assumed here. -/
namespace ThreeCompactParameter318
set_option maxHeartbeats 0

@[expose] def quartic (z x : ℂ) : ℂ :=
  (z-1728)^2*x^4-6*z*(z-1728)*x^2-8*z*(z-1728)*x-3*z^2

@[expose] def D (t : ℂ) : ℂ := t^2-486*t-19683
@[expose] def J (t : ℂ) : ℂ := (t+27)*(t+243)^3/t^3
@[expose] def X (t : ℂ) : ℂ := 3*(t+27)*(t+243)/D t
@[expose] def numerator (z x : ℂ) : ℂ := (z-1728)*x^2-z
@[expose] def denominator (z x : ℂ) : ℂ := 9*z-(z-1728)*x^2
@[expose] def parameter (z x : ℂ) : ℂ := 243*numerator z x/denominator z x

lemma J_sub_1728 (t : ℂ) (ht : t ≠ 0) :
    J t-1728=(D t)^2/t^3 := by
  unfold J D
  field_simp
  ring

lemma quartic_parametrization (t : ℂ) (ht : t ≠ 0) (hd : D t ≠ 0) :
    quartic (J t) (X t)=0 := by
  unfold quartic J X
  field_simp
  unfold D
  ring

lemma numerator_parametrization (t : ℂ) (ht : t ≠ 0) (hd : D t ≠ 0) :
    numerator (J t) (X t)=8*(t+27)*(t+243)^2/t^2 := by
  unfold numerator J X
  field_simp
  unfold D
  ring

lemma denominator_parametrization (t : ℂ) (ht : t ≠ 0) (hd : D t ≠ 0) :
    denominator (J t) (X t)=1944*(t+27)*(t+243)^2/t^3 := by
  unfold denominator J X
  field_simp
  unfold D
  ring

lemma parameter_parametrization (t : ℂ) (ht : t ≠ 0)
    (h27 : t+27 ≠ 0) (h243 : t+243 ≠ 0) (hd : D t ≠ 0) :
    parameter (J t) (X t)=t := by
  rw [parameter,numerator_parametrization t ht hd,denominator_parametrization t ht hd]
  field_simp
  ring

lemma quartic_x_ne_zero {z x : ℂ} (hz : z ≠ 0) (hq : quartic z x=0) : x ≠ 0 := by
  intro hx
  subst x
  have hh : z^2=0 := by
    unfold quartic at hq
    linear_combination (-1/3:ℂ)*hq
  exact hz ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hh)

lemma reduced_numerator_ne_zero {k x : ℂ} (hk : k ≠ 0) (hk1 : k ≠ 1)
    (hq : x^4-6*k*x^2-8*k*x-3*k^2=0) : x^2-k ≠ 0 := by
  intro ha
  have hh : x^3*(x+1)=0 := by
    linear_combination (1/8:ℂ)*(3*k+9*x^2+8*x)*ha-(1/8:ℂ)*hq
  rcases mul_eq_zero.mp hh with hx | hx
  · have hx0 : x=0 := (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hx
    apply hk
    subst x
    linear_combination -ha
  · have hx1 : x = -1 := by linear_combination hx
    apply hk1
    rw [hx1] at ha
    linear_combination -ha

lemma reduced_denominator_ne_zero {k x : ℂ} (hk : k ≠ 0) (hk1 : k ≠ 1)
    (hq : x^4-6*k*x^2-8*k*x-3*k^2=0) : 9*k-x^2 ≠ 0 := by
  intro hb
  have hh : x^3*(x-3)=0 := by
    linear_combination (27/8:ℂ)*hq+(1/8:ℂ)*(9*k+19*x^2+24*x)*hb
  rcases mul_eq_zero.mp hh with hx | hx
  · have hx0 : x=0 := (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hx
    apply hk
    subst x
    linear_combination (1/9:ℂ)*hb
  · have hx3 : x=3 := by linear_combination hx
    apply hk1
    rw [hx3] at hb
    linear_combination (1/9:ℂ)*hb

lemma normalized_quartic {z x : ℂ} (hz : z ≠ 1728) (hq : quartic z x=0) :
    x^4-6*(z/(z-1728))*x^2-8*(z/(z-1728))*x-3*(z/(z-1728))^2=0 := by
  have hs : z-1728 ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  unfold quartic at hq
  linear_combination hq

lemma ratio_ne_one {z : ℂ} (hz : z ≠ 1728) : z/(z-1728) ≠ 1 := by
  intro he
  have hh := (div_eq_one_iff_eq (sub_ne_zero.mpr hz)).mp he
  have : (1728:ℂ)=0 := by linear_combination hh
  norm_num at this

lemma numerator_ne_zero {z x : ℂ} (hz : z ≠ 0) (h1728 : z ≠ 1728)
    (hq : quartic z x=0) : numerator z x ≠ 0 := by
  have hs : z-1728 ≠ 0 := sub_ne_zero.mpr h1728
  have hn := reduced_numerator_ne_zero (div_ne_zero hz hs)
    (ratio_ne_one h1728) (normalized_quartic h1728 hq)
  have he : numerator z x=(z-1728)*(x^2-z/(z-1728)) := by
    unfold numerator
    field_simp
  rw [he]
  exact mul_ne_zero hs hn

lemma denominator_ne_zero {z x : ℂ} (hz : z ≠ 0) (h1728 : z ≠ 1728)
    (hq : quartic z x=0) : denominator z x ≠ 0 := by
  have hs : z-1728 ≠ 0 := sub_ne_zero.mpr h1728
  have hn := reduced_denominator_ne_zero (div_ne_zero hz hs)
    (ratio_ne_one h1728) (normalized_quartic h1728 hq)
  have he : denominator z x=(z-1728)*(9*(z/(z-1728))-x^2) := by
    unfold denominator
    field_simp
  rw [he]
  exact mul_ne_zero hs hn

lemma D_parameter {z x : ℂ} (hb : denominator z x ≠ 0) (hq : quartic z x=0) :
    D (parameter z x)=1259712*x*z*(z-1728)/(denominator z x)^2 := by
  unfold D parameter
  field_simp
  unfold numerator denominator quartic at *
  linear_combination 157464*hq

lemma parameter_ne_zero {z x : ℂ} (hz : z ≠ 0) (h1728 : z ≠ 1728)
    (hq : quartic z x=0) : parameter z x ≠ 0 := by
  unfold parameter
  exact div_ne_zero (mul_ne_zero (by norm_num) (numerator_ne_zero hz h1728 hq))
    (denominator_ne_zero hz h1728 hq)

lemma D_parameter_ne_zero {z x : ℂ} (hz : z ≠ 0) (h1728 : z ≠ 1728)
    (hq : quartic z x=0) : D (parameter z x) ≠ 0 := by
  have hb := denominator_ne_zero hz h1728 hq
  rw [D_parameter hb hq]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (quartic_x_ne_zero hz hq)) hz) (sub_ne_zero.mpr h1728)) (pow_ne_zero _ hb)

lemma X_parameter {z x : ℂ} (hz : z ≠ 0) (h1728 : z ≠ 1728)
    (hq : quartic z x=0) : X (parameter z x)=x := by
  have hb := denominator_ne_zero hz h1728 hq
  have hx := quartic_x_ne_zero hz hq
  have hs := sub_ne_zero.mpr h1728
  rw [X,D_parameter hb hq]
  unfold parameter
  field_simp
  unfold numerator denominator quartic at *
  ring

lemma J_parameter {z x : ℂ} (hz : z ≠ 0) (h1728 : z ≠ 1728)
    (hq : quartic z x=0) : J (parameter z x)=z := by
  have hb := denominator_ne_zero hz h1728 hq
  have ha := numerator_ne_zero hz h1728 hq
  unfold J parameter
  field_simp
  unfold numerator denominator quartic at *
  linear_combination z *
    ((z-1728)^2*x^4-6*z*(z-1728)*x^2+8*z*(z-1728)*x-3*z^2)*hq

lemma J_ne_zero_iff {t : ℂ} (ht : t ≠ 0) :
    J t ≠ 0 ↔ t+27 ≠ 0 ∧ t+243 ≠ 0 := by
  simp [J,ht]

lemma J_ne_1728_iff {t : ℂ} (ht : t ≠ 0) : J t ≠ 1728 ↔ D t ≠ 0 := by
  rw [←sub_ne_zero,J_sub_1728 t ht]
  simp [ht]

/-- Exactly the parameter open corresponding to the existing j-open family.
The six deleted points are not silently filled by this definition. -/
abbrev ParameterOpen := {t : ℂ // t ≠ 0 ∧ t+27 ≠ 0 ∧ t+243 ≠ 0 ∧ D t ≠ 0}
abbrev PlaneOpen := {p : ℂ × ℂ // p.1 ≠ 0 ∧ p.1 ≠ 1728 ∧ quartic p.1 p.2=0}

@[expose] def toPlane (t : ParameterOpen) : PlaneOpen :=
  ⟨(J t.val,X t.val),(J_ne_zero_iff t.property.1).mpr
      ⟨t.property.2.1,t.property.2.2.1⟩,
    (J_ne_1728_iff t.property.1).mpr t.property.2.2.2,
    quartic_parametrization t.val t.property.1 t.property.2.2.2⟩

@[expose] def fromPlane (p : PlaneOpen) : ParameterOpen := by
  have ht := parameter_ne_zero p.property.1 p.property.2.1 p.property.2.2
  have hj := J_parameter p.property.1 p.property.2.1 p.property.2.2
  have hjn : J (parameter p.val.1 p.val.2) ≠ 0 := by
    rw [hj]
    exact p.property.1
  have hn := (J_ne_zero_iff ht).mp hjn
  exact ⟨parameter p.val.1 p.val.2,ht,hn.1,hn.2,
    D_parameter_ne_zero p.property.1 p.property.2.1 p.property.2.2⟩

/-- An explicit inverse on every point of the actual open quartic, not just
a generic rational function-field identity or a point-count comparison. -/
@[expose] def openEquiv : ParameterOpen ≃ PlaneOpen where
  toFun := toPlane
  invFun := fromPlane
  left_inv t := by
    apply Subtype.ext
    exact parameter_parametrization t.val t.property.1 t.property.2.1
      t.property.2.2.1 t.property.2.2.2
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (J_parameter p.property.1 p.property.2.1 p.property.2.2)
      (X_parameter p.property.1 p.property.2.1 p.property.2.2)

lemma toPlane_continuous : Continuous toPlane := by
  have hj : Continuous (fun t : ParameterOpen => J t.val) := by
    unfold J
    apply Continuous.div
    · fun_prop
    · fun_prop
    · exact fun t => pow_ne_zero _ t.property.1
  have hx : Continuous (fun t : ParameterOpen => X t.val) := by
    unfold X
    apply Continuous.div
    · fun_prop
    · unfold D; fun_prop
    · exact fun t => t.property.2.2.2
  exact (hj.prodMk hx).subtype_mk _

lemma fromPlane_continuous : Continuous fromPlane := by
  have hp : Continuous (fun p : PlaneOpen => parameter p.val.1 p.val.2) := by
    unfold parameter
    apply Continuous.div
    · unfold numerator; fun_prop
    · unfold denominator; fun_prop
    · exact fun p => denominator_ne_zero p.property.1 p.property.2.1 p.property.2.2
  exact hp.subtype_mk _

/-- Both original subspace topologies, with the explicit rational inverse. -/
@[expose] def openHomeomorph : ParameterOpen ≃ₜ PlaneOpen where
  toEquiv := openEquiv
  continuous_toFun := toPlane_continuous
  continuous_invFun := fromPlane_continuous

/-- Cleared derivative numerator for the degree-four rational j map. -/
lemma derivative_numerator (t : ℂ) :
    ((t+243)^3+3*(t+27)*(t+243)^2)*t-
      3*(t+27)*(t+243)^3=(t+243)^2*D t := by
  unfold D
  ring

/-- The reciprocal parameter s=1/t supplies the other projective chart. -/
lemma J_reciprocal (s : ℂ) (hs : s ≠ 0) :
    J s⁻¹=(1+27*s)*(1+243*s)^3/s := by
  unfold J
  field_simp

/-- Exact numerator identities retain the local order data at both cusps. -/
lemma cusp_numerator_zero : (0+27:ℂ)*(0+243)^3=387420489 := by norm_num
lemma cusp_numerator_infinity : (1+27*(0:ℂ))*(1+243*0)^3=1 := by norm_num
lemma elliptic_zero_simple : ((-27:ℂ)+243)^3=10077696 := by norm_num
lemma elliptic_zero_triple : (-243:ℂ)+27 = -216 := by norm_num
lemma D_at_zero : D 0 = -19683 := by norm_num [D]
lemma D_at_simple_zero : D (-27) = -5832 := by norm_num [D]
lemma D_at_triple_zero : D (-243) = 157464 := by norm_num [D]

end ThreeCompactParameter318
