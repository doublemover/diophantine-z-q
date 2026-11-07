module

public import Mathlib.Tactic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Nat.Squarefree

/-!
# Algebraic certificates for quartic witness optimization

This auxiliary development proves local identities and witness-set equivalences.
It does not assert that any concrete polynomial defines the integers. The
arithmetic characterization of the source circuit is a separate obligation.
The square-abscissa chart theorem displays its arithmetic hypothesis explicitly.
-/

public section

namespace QuarticOptimization

section Field

variable {K : Type*} [Field K]

/-- A constant nonzero pivot can be eliminated without changing existential
solvability or any other condition on the remaining coordinates. -/
theorem eliminate_constant_pivot (c f : K) (hc : c ≠ 0) (P : K → Prop) :
    (∃ y, c * y + f = 0 ∧ P y) ↔ P (-f / c) := by
  constructor
  · rintro ⟨y, hy, hP⟩
    have heq : y = -f / c := by
      apply (eq_div_iff hc).2
      linear_combination hy
    simpa [heq] using hP
  · intro hP
    refine ⟨-f / c, ?_, hP⟩
    field_simp [hc]
    ring

/-- An invertible triangular shear preserves arbitrary witness predicates. -/
theorem exists_shear_iff {ι : Type*} (P : K → (ι → K) → Prop) :
    (∃ (b : K) (v : ι → K), P b v) ↔
      (∃ (b : K) (w : ι → K), P b (fun i => w i - b)) := by
  constructor
  · rintro ⟨b, v, hv⟩
    refine ⟨b, (fun i => v i + b), ?_⟩
    simpa using hv
  · rintro ⟨b, w, hw⟩
    exact ⟨b, (fun i => w i - b), hw⟩

/-- Adding a polynomial multiple of one residual to another is reversible. -/
theorem row_add_iff (a b k : K) :
    (a = 0 ∧ b = 0) ↔ (a = 0 ∧ b + k * a = 0) := by
  constructor <;> rintro ⟨ha, hb⟩ <;> simp_all

/-- A nonzero scale does not alter a zero set. -/
theorem scale_zero_iff (a b : K) (hb : b ≠ 0) :
    b * a = 0 ↔ a = 0 := by
  simp [hb]

/-! ## Coordinate-pole rescaling -/

def poleFirstOld (b p r : K) : K := 17*p^2 - b*(289 + 34*r - 3*r^2)

def poleFirstNew (b p r w : K) : K :=
  17*p^2 - 289*b - 578*r + 34*w + 51*r^2 - 3*r*w

theorem pole_first_residual_identity (b p r w : K) :
    poleFirstNew b p r w - poleFirstOld b p r =
      (34 - 3*r)*(w - 17*r + b*r) := by
  unfold poleFirstNew poleFirstOld
  ring

theorem pole_first_equivalent (b p r w : K) (hw : w = r*(17-b)) :
    poleFirstNew b p r w = 0 ↔ poleFirstOld b p r = 0 := by
  have heq : poleFirstNew b p r w = poleFirstOld b p r := by
    rw [hw]
    unfold poleFirstNew poleFirstOld
    ring
  rw [heq]

theorem pole_rescale_first (b p r : K) :
    17*b*p^2 - (17*b-b*r)*(17*b+3*b*r) = b*poleFirstOld b p r := by
  unfold poleFirstOld
  ring

theorem pole_rescale_second (b q s w : K) :
    17*b*(b*q)^2 - ((b*s)^2-b^2*w)*((b*s)^2+3*b^2*w) =
      b^3*(17*q^2-b*(s^2-w)*(s^2+3*w)) := by
  ring

/-! ## Square-abscissa point chart -/

def oldPointChart (D x y : K) : Prop :=
  ∃ t h, h^2 = x ∧ t^2*(x-t^2/4) = D ∧ y = h*(t^2/2-x)

def squarePointChart (D x y : K) : Prop :=
  ∃ h m, h^2 = x ∧ m^2 = x^2-D ∧ y = h*m

/-- This is the precise extra arithmetic input. It is not asserted here for
the concrete quadratic field. -/
def DualSquareAbscissa (D : K) : Prop :=
  ∀ a v : K, a ≠ 0 → v^2 = a^3 + 4*D*a → ∃ t : K, t^2 = a

theorem old_chart_implies_square [CharZero K] (D x y : K) :
    oldPointChart D x y → squarePointChart D x y := by
  rintro ⟨t, h, hx, hD, hy⟩
  refine ⟨h, t^2/2-x, hx, ?_, hy⟩
  linear_combination -hD

theorem square_chart_point_on_curve (D x y : K)
    (hchart : squarePointChart D x y) : y^2 = x^3-D*x := by
  rcases hchart with ⟨h, m, hx, hm, rfl⟩
  calc
    (h*m)^2 = h^2*m^2 := by ring
    _ = x*(x^2-D) := by rw [hx, hm]
    _ = x^3-D*x := by ring

theorem square_chart_implies_old [CharZero K] (D x y : K) (hD : D ≠ 0)
    (hdual : DualSquareAbscissa D) :
    squarePointChart D x y → oldPointChart D x y := by
  rintro ⟨h, m, hx, hm, hy⟩
  have ha : 2*(x+m) ≠ 0 := by
    intro hz
    have hxm : m = -x := by linear_combination hz / 2
    apply hD
    rw [hxm] at hm
    linear_combination hm
  have hv : (2*h*(2*(x+m)))^2 = (2*(x+m))^3+4*D*(2*(x+m)) := by
    linear_combination 16*(x+m)^2*hx - 8*(x+m)*hm
  obtain ⟨t, ht⟩ := hdual _ _ ha hv
  refine ⟨t, h, hx, ?_, ?_⟩
  · rw [ht]
    linear_combination -hm
  · rw [ht, hy]
    ring

theorem point_chart_equivalence [CharZero K] (D x y : K) (hD : D ≠ 0)
    (hdual : DualSquareAbscissa D) :
    oldPointChart D x y ↔ squarePointChart D x y :=
  ⟨old_chart_implies_square D x y, square_chart_implies_old D x y hD hdual⟩

/-! ## Omission of ordinates from square-abscissa charts -/

theorem parameter_ordinate_omission (h m z : K) (hh : h ≠ 0) :
    h*m*z = -h^2 ↔ m*z = -h := by
  constructor
  · intro heq
    apply (mul_left_cancel₀ hh)
    linear_combination heq
  · intro heq
    linear_combination h*heq

theorem logarithm_ordinate_omission (h m ell out : K) (hh : h ≠ 0) :
    h*m*ell = -h^2*out ↔ m*ell = -h*out := by
  constructor
  · intro heq
    apply (mul_left_cancel₀ hh)
    linear_combination heq
  · intro heq
    linear_combination h*heq

theorem ratio_ordinate_omission (h m rho z : K) (hh : h ≠ 0) :
    h^2*rho = -h*m*z ↔ h*rho = -m*z := by
  constructor
  · intro heq
    apply (mul_left_cancel₀ hh)
    linear_combination heq
  · intro heq
    linear_combination h*heq

/-! ## Complete difference equation: the tangent specialization -/

theorem complete_difference_at_equal_x (a b slope v D : K) :
    (a-a)*v - 2*b*slope - a*a - 2*a^2 + D = 0 ↔
      2*b*slope = D-3*a^2 := by
  constructor <;> intro h <;> linear_combination -h

/-- The saturated chord equation follows from the original guarded chord
equations. This is a polynomial certificate, before cancellation of x-a. -/
theorem complete_difference_identity (x a y b slope v D : K) :
    (x-a)*((x-a)*v-2*b*slope-x*a-2*a^2+D) =
      (x-a)^2*(v-slope^2+x+a) +
      ((x-a)*slope+y-b)*((x-a)*slope-y-b) +
      (y^2-x^3+D*x) - (b^2-a^3+D*a) := by
  ring

theorem guarded_difference_implies_complete (x a y b slope v D : K)
    (hxa : x ≠ a) (hx : y^2 = x^3-D*x) (ha : b^2 = a^3-D*a)
    (hs : (x-a)*slope = y+b) (hv : v = slope^2-x-a) :
    (x-a)*v-2*b*slope-x*a-2*a^2+D = 0 := by
  have hid := complete_difference_identity x a y b slope v D
  have hprod : (x-a)*((x-a)*v-2*b*slope-x*a-2*a^2+D) = 0 := by
    linear_combination hid + (x-a)^2*hv +
      ((x-a)*slope+y-b)*hs + hx - ha
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hxa)

/-- The first chord equation excludes the coincident point when the root
ordinate is nonzero; the equal-abscissa case is the opposite point. -/
theorem complete_difference_equal_x_opposite (x a y b slope : K)
    (hxa : x = a) (hs : (x-a)*slope = y+b) : y = -b := by
  rw [hxa] at hs
  linear_combination -hs

/-! ## The scalar conic chart -/

theorem scalar_conic_parametrization (b t : K) (hd : 1+b*t^2 ≠ 0) :
    ((1-b*t^2)/(1+b*t^2))^2 + b*(2*t/(1+b*t^2))^2 = 1 := by
  field_simp [hd]
  ring

theorem scalar_conic_exception (b u v : K) (hb : b ≠ 0)
    (hc : u^2+b*v^2 = 1) (hu : u = -1) : v = 0 := by
  rw [hu] at hc
  have hv : b*v^2 = 0 := by linear_combination hc
  exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp hv).resolve_left hb)

theorem scalar_conic_inverse_denominator (b u v : K)
    (hc : u^2+b*v^2 = 1) (hu : 1+u ≠ 0) :
    1+b*(v/(1+u))^2 = 2/(1+u) := by
  field_simp [hu]
  linear_combination hc

theorem scalar_conic_inverse [CharZero K] (b u v : K)
    (hc : u^2+b*v^2 = 1) (hu : 1+u ≠ 0) :
    ∃ t : K, 1+b*t^2 ≠ 0 ∧
      u = (1-b*t^2)/(1+b*t^2) ∧ v = 2*t/(1+b*t^2) := by
  refine ⟨v/(1+u), ?_, ?_, ?_⟩
  · rw [scalar_conic_inverse_denominator b u v hc hu]
    exact div_ne_zero (by norm_num) hu
  · rw [scalar_conic_inverse_denominator b u v hc hu]
    field_simp [hu]
    linear_combination hc
  · rw [scalar_conic_inverse_denominator b u v hc hu]
    field_simp [hu]

/-- The exceptional conic point can be reflected without changing the only
quantity consumed by the source pole gadget, namely u squared. -/
theorem scalar_conic_squared_cover [CharZero K] (b u v : K)
    (hc : u^2+b*v^2 = 1) :
    ∃ t : K, 1+b*t^2 ≠ 0 ∧
      u^2 = ((1-b*t^2)/(1+b*t^2))^2 := by
  by_cases hu : 1+u = 0
  · have hum : u = -1 := by linear_combination hu
    exact ⟨0, by norm_num, by simp [hum]⟩
  · obtain ⟨t, ht, htu, _⟩ := scalar_conic_inverse b u v hc hu
    exact ⟨t, ht, by rw [htu]⟩

theorem scalar_pole_first_identity (b p r j a w : K)
    (ha : a = r*j) (hw : w = 17*r-b*r+j*a) :
    17*p^2-289*b-578*r-34*j*a+34*w+51*r^2+3*a^2-3*r*w =
      17*p^2-b*(289+34*r-3*r^2) := by
  rw [hw, ha]
  ring

theorem scalar_pole_h_identity (b u v r j a w : K)
    (hc : u^2+b*v^2 = 1) (hj : j = b*v) (ha : a = r*j)
    (hw : w = 17*r-b*r+j*a) :
    (b*r)*(17*b-(b*u)^2) = b^2*w := by
  rw [hw, ha, hj]
  linear_combination -b^3*r*hc

/-! ## Complete differences in square-abscissa coordinates -/

theorem jacobi_chord_identity (h a slope k : K) :
    (h^2-a^2)*slope = h*(h*slope-a*k)+a*(h*k-a*slope) := by
  ring

theorem jacobi_ordinate_identity (h a slope k : K) :
    slope*(h^2-k^2)-h*(h*slope-a*k) = k*(h*a-slope*k) := by
  ring

theorem jacobi_curve_identity (h a slope k : K) :
    (h*a-slope*k)^2-k^4+(h^4-(h*slope-a*k)^2) =
      (h^2-k^2)*(a^2+h^2+k^2-slope^2) := by
  ring

theorem jacobi_complete_difference_identity (h a slope k : K) :
    (h^2-a^2)*k^2-2*a*(h*k-a*slope)*slope-h^2*a^2-2*a^4+
      (h^4-(h*slope-a*k)^2) =
      (h^2-2*a^2)*(a^2+h^2+k^2-slope^2) := by
  ring

theorem four_scaled_anchor_identity (h u n L : K) :
    4*(L-n) = (h*L-4*u)-((h-4)*L-4*(u-n)) := by
  ring

theorem four_scaled_ratios_recover_label [CharZero K] (h u n L : K)
    (hfirst : h*L = 4*u) (hsecond : (h-4)*L = 4*(u-n)) : L = n := by
  linear_combination (hfirst-hsecond)/4

/-! ## Reciprocal quartic chart at finite points -/

theorem reciprocal_chart_to_square_chart (D u v : K) (hu : u ≠ 0)
    (hc : v^2 = 1-D*u^4) :
    squarePointChart D (1/u^2) (v/u^3) := by
  refine ⟨1/u, v/u^2, ?_, ?_, ?_⟩
  · field_simp [hu]
  · field_simp [hu]
    linear_combination hc
  · field_simp [hu]

theorem reciprocal_chart_curve (D u v : K) (hu : u ≠ 0)
    (hc : v^2 = 1-D*u^4) :
    (v/u^3)^2 = (1/u^2)^3-D*(1/u^2) :=
  square_chart_point_on_curve D _ _ (reciprocal_chart_to_square_chart D u v hu hc)

theorem reciprocal_chart_parameter (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) :
    -(1/u^2)/(v/u^3) = -u/v := by
  field_simp [hu, hv]

theorem reciprocal_chart_boundary (D v : K) (hc : v^2 = 1-D*(0 : K)^4) :
    v = 1 ∨ v = -1 := by
  have hs : v^2 = (1 : K)^2 := by simpa using hc
  exact eq_or_eq_neg_of_sq_eq_sq v 1 hs

theorem fixed_translation_saturation_identity (D k m u v a : K) :
    (k^2+D*u^2)*(1-2*m*u*a-D*u^2*a^2-k^2*(u^2+a^2)) =
      (k*v-m*u-a*(k^2+D*u^2))*(k*v+m*u+a*(k^2+D*u^2)) -
      k^2*(v^2-1+D*u^4)+(m^2-k^4+D)*u^2 := by
  ring

theorem fixed_translation_saturation (D k m u v a : K)
    (hB : k^2+D*u^2 ≠ 0) (hfixed : m^2 = k^4-D)
    (hcurve : v^2 = 1-D*u^4) (htranslate : k*v = m*u+a*(k^2+D*u^2)) :
    1-2*m*u*a-D*u^2*a^2-k^2*(u^2+a^2) = 0 := by
  have hid := fixed_translation_saturation_identity D k m u v a
  have hp : (k^2+D*u^2)*(1-2*m*u*a-D*u^2*a^2-k^2*(u^2+a^2)) = 0 := by
    linear_combination hid +
      (k*v+m*u+a*(k^2+D*u^2))*htranslate-k^2*hcurve+u^2*hfixed
  exact (mul_eq_zero.mp hp).resolve_left hB

theorem fixed_translation_first_identity (D k m u v a : K) :
    k*a*v+m*u*a+k^2*u^2-1 +
      (1-2*m*u*a-D*u^2*a^2-k^2*(u^2+a^2)) =
      a*(k*v-m*u-k^2*a-D*u^2*a) := by
  ring

theorem fixed_translation_second_identity (D k m u a b : K) :
    k*u*b-m*u*a-k^2*a^2+1 -
      (1-2*m*u*a-D*u^2*a^2-k^2*(u^2+a^2)) =
      u*(k*b+m*a+k^2*u+D*u*a^2) := by
  ring


def fixedAnchorResidual (D k m u w : K) : K :=
  1-k^2*(u^2+u^2*w^2)-2*m*u^2*w-D*u^4*w^2

theorem fixed_anchor_compression_first (D k m u w : K) :
    (u*(m+D*u^2*w+k^2*w))^2-k^2*(1-D*u^4) =
      -(D*u^2+k^2)*fixedAnchorResidual D k m u w+
      u^2*(m^2-k^4+D) := by
  unfold fixedAnchorResidual
  ring

theorem fixed_anchor_compression_second (D k m u w : K) :
    (u*(m*w+D*u^2*w^2+k^2))^2-k^2*(1-D*(u*w)^4) =
      -(D*u^2*w^2+k^2)*fixedAnchorResidual D k m u w+
      (u*w)^2*(m^2-k^4+D) := by
  unfold fixedAnchorResidual
  ring

theorem fixed_anchor_compression_nonzero (D k m u w : K)
    (h : fixedAnchorResidual D k m u w = 0) : u ≠ 0 := by
  intro hu
  simp [fixedAnchorResidual, hu] at h


end Field

noncomputable def reciprocalLogPolynomial (cs : List (ℚ × ℕ)) (w : ℝ) : ℝ :=
  1+(cs.map (fun c => (c.1 : ℝ)*w^c.2)).sum

theorem reciprocalLogPolynomial_lower (cs : List (ℚ × ℕ))
    (hcs : ∀ c ∈ cs, c.1 ≤ 0) (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    1+(cs.map (fun c => (c.1 : ℝ))).sum ≤ reciprocalLogPolynomial cs w := by
  induction cs with
  | nil => simp [reciprocalLogPolynomial]
  | cons c cs ih =>
    have hc : c.1 ≤ 0 := hcs c (by simp)
    have ht : (c.1 : ℝ) ≤ (c.1 : ℝ)*w^c.2 := by
      simpa using mul_le_mul_of_nonpos_left (pow_le_one₀ hw0 hw1) (by exact_mod_cast hc)
    have hs : ∀ x ∈ cs, x.1 ≤ 0 := by
      intro x hx
      exact hcs x (by simp [hx])
    have hi := ih hs
    simp only [reciprocalLogPolynomial, List.map_cons, List.sum_cons] at hi ⊢
    linarith

def reciprocalLogCoefficients16 : List (ℚ × ℕ) :=
  [(-2/5,1),(-2/15,2),(-14/195,3)]

def reciprocalLogCoefficients52 : List (ℚ × ℕ) :=
  [(-2/5,1),(-2/15,2),(-14/195,3),(-154/3315,4),(-22/663,5),
   (-418/16575,6),(-9614/480675,7),(-2622/160225,8),(-81282/5928325,9),
   (-568974/48612265,10),(-189658/18697025,11),(-1165042/130879175,12)]

theorem reciprocalLog16_positive (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 < reciprocalLogPolynomial reciprocalLogCoefficients16 w := by
  have hcs : ∀ c ∈ reciprocalLogCoefficients16, c.1 ≤ 0 := by
    norm_num [reciprocalLogCoefficients16]
  have h := reciprocalLogPolynomial_lower reciprocalLogCoefficients16 hcs w hw0 hw1
  norm_num [reciprocalLogCoefficients16] at h
  norm_num [reciprocalLogCoefficients16]
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 77/195) h

theorem reciprocalLog52_positive (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    0 < reciprocalLogPolynomial reciprocalLogCoefficients52 w := by
  have hcs : ∀ c ∈ reciprocalLogCoefficients52, c.1 ≤ 0 := by
    norm_num [reciprocalLogCoefficients52]
  have h := reciprocalLogPolynomial_lower reciprocalLogCoefficients52 hcs w hw0 hw1
  norm_num [reciprocalLogCoefficients52] at h
  norm_num [reciprocalLogCoefficients52]
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 27378487/130879175) h

theorem rational_sum_squares_zero (xs : List ℚ) :
    (xs.map (fun x => x^2)).sum = 0 ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hn : 0 ≤ (xs.map (fun x => x^2)).sum := by
      exact List.sum_nonneg (by simp only [List.mem_map]; rintro a ⟨b, _, rfl⟩; exact sq_nonneg b)
    simp only [List.map_cons, List.sum_cons, List.forall_mem_cons]
    rw [add_eq_zero_iff_of_nonneg (sq_nonneg x) hn,
      pow_eq_zero_iff (by decide : 2 ≠ 0), ih]

noncomputable def quadraticSOS {σ : Type*} (ps : List (MvPolynomial σ ℚ)) : MvPolynomial σ ℚ :=
  (ps.map (fun p => p^2)).sum

theorem quadraticSOS_zero_iff {σ : Type*} (ps : List (MvPolynomial σ ℚ))
    (x : σ → ℚ) :
    MvPolynomial.eval x (quadraticSOS ps) = 0 ↔
      ∀ p ∈ ps, MvPolynomial.eval x p = 0 := by
  simpa [quadraticSOS, map_list_sum, List.map_map, Function.comp_def] using
    rational_sum_squares_zero (ps.map (MvPolynomial.eval x))

/-- Keeping every residual quadratic guarantees a polynomial of degree at
most four. Exact degree four for a concrete output still needs a nonzero
degree-four coefficient, supplied by the separate concrete coefficient audit. -/
theorem quadraticSOS_degree_le_four {σ : Type*} (ps : List (MvPolynomial σ ℚ))
    (hdegree : ∀ p ∈ ps, p.totalDegree ≤ 2) :
    (quadraticSOS ps).totalDegree ≤ 4 := by
  induction ps with
  | nil => simp [quadraticSOS]
  | cons p ps ih =>
    have hp : p.totalDegree ≤ 2 := hdegree p (by simp)
    have hps : ∀ q ∈ ps, q.totalDegree ≤ 2 := by
      intro q hq
      exact hdegree q (by simp [hq])
    have hpow : (p^2).totalDegree ≤ 4 :=
      (MvPolynomial.totalDegree_pow p 2).trans (by omega)
    simpa only [quadraticSOS, List.map_cons, List.sum_cons] using
      (MvPolynomial.totalDegree_add (p^2) (quadraticSOS ps)).trans
        (max_le hpow (ih hps))

/-- The shifted input beta=2*q^2+c is integral exactly when q is integral.
The key converse is stronger than merely assuming q squared integral. -/
theorem twice_square_integral (q : ℚ) (n : ℤ) (hn : 2*q^2 = n) :
    ∃ z : ℤ, (z : ℚ) = q := by
  have hq : q^2 = Rat.divInt n 2 := by
    rw [Rat.divInt_eq_div]
    linear_combination hn / 2
  have hdvd : (q.den^2 : ℕ) ∣ 2 := by
    have hd := Rat.den_dvd n 2
    rw [← hq, Rat.den_pow] at hd
    exact_mod_cast hd
  have hle : q.den^2 ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  have hpos := q.den_pos
  have hd : q.den = 1 := by nlinarith
  exact ⟨q.num, Rat.coe_int_num_of_den_eq_one hd⟩

theorem shifted_twice_square_integral (q : ℚ) (c : ℤ) :
    (∃ n : ℤ, 2*q^2+c = n) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  constructor
  · rintro ⟨n, hn⟩
    apply twice_square_integral q (n-c)
    push_cast
    linear_combination hn
  · rintro ⟨z, rfl⟩
    exact ⟨2*z^2+c, by push_cast; ring⟩

theorem squarefree_multiple_square_integral (q : ℚ) (a : ℕ)
    (ha : Squarefree a) (n : ℤ) (hn : (a : ℚ)*q^2 = n) :
    ∃ z : ℤ, (z : ℚ) = q := by
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne_zero
  have hq : q^2 = Rat.divInt n a := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    apply (eq_div_iff haQ).2
    linear_combination hn
  have hdvd : (q.den^2 : ℕ) ∣ a := by
    have hd := Rat.den_dvd n a
    rw [← hq, Rat.den_pow] at hd
    exact_mod_cast hd
  have hunit : IsUnit q.den := ha q.den (by simpa [pow_two] using hdvd)
  have hd : q.den = 1 := by simpa using hunit
  exact ⟨q.num, Rat.coe_int_num_of_den_eq_one hd⟩

theorem shifted_squarefree_square_integral (q : ℚ) (a : ℕ)
    (ha : Squarefree a) (c : ℤ) :
    (∃ n : ℤ, (a : ℚ)*q^2+c = n) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  constructor
  · rintro ⟨n, hn⟩
    apply squarefree_multiple_square_integral q a ha (n-c)
    push_cast
    linear_combination hn
  · rintro ⟨z, rfl⟩
    exact ⟨(a : ℤ)*z^2+c, by push_cast; ring⟩

theorem nat_102_squarefree : Squarefree (102 : ℕ) := by
  intro d hd
  have hle : d*d ≤ 102 := Nat.le_of_dvd (by decide) hd
  have hdle : d ≤ 10 := by nlinarith
  interval_cases d
  all_goals norm_num at hd
  all_goals norm_num

theorem input_102_4643_integral (q : ℚ) :
    (∃ n : ℤ, 102*q^2+4643 = n) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  simpa using shifted_squarefree_square_integral q 102 nat_102_squarefree 4643

theorem powerfree_multiple_power_integral (q : ℚ) (a k : ℕ)
    (ha : a ≠ 0) (hfree : ∀ d : ℕ, d^k ∣ a → d = 1)
    (n : ℤ) (hn : (a : ℚ)*q^k = n) : ∃ z : ℤ, (z : ℚ) = q := by
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hq : q^k = Rat.divInt n a := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
    apply (eq_div_iff haQ).2
    linear_combination hn
  have hdvd : (q.den^k : ℕ) ∣ a := by
    have hd := Rat.den_dvd n a
    rw [← hq, Rat.den_pow] at hd
    exact_mod_cast hd
  exact ⟨q.num, Rat.coe_int_num_of_den_eq_one (hfree q.den hdvd)⟩

theorem nat_1224_fourth_powerfree (d : ℕ) (hd : d^4 ∣ 1224) : d = 1 := by
  have hle : d^4 ≤ 1224 := Nat.le_of_dvd (by decide) hd
  have hdle : d ≤ 5 := by nlinarith [sq_nonneg (d^2-36 : ℤ)]
  interval_cases d
  all_goals norm_num at hd
  all_goals rfl

theorem input_1224_2739_integral (q : ℚ) :
    (∃ n : ℤ, 1224*q^4+2739 = n) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  constructor
  · rintro ⟨n, hn⟩
    apply powerfree_multiple_power_integral q 1224 4 (by decide)
      nat_1224_fourth_powerfree (n-2739)
    push_cast
    linear_combination hn
  · rintro ⟨z, rfl⟩
    exact ⟨1224*z^4+2739, by push_cast; ring⟩

theorem input_nested_102_321_integral (q : ℚ) :
    (∃ n : ℤ, (102*q^2+321)^2+1 = n) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ :=
      (shifted_squarefree_square_integral (102*q^2+321) 1 squarefree_one 1).mp
        (by simpa using h)
    exact (shifted_squarefree_square_integral q 102 nat_102_squarefree 321).mp
      ⟨n, hn.symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨(102*z^2+321)^2+1, by push_cast; ring⟩

/-! ## Conditional transfer of a characterization

The hypothesis `source` is deliberately visible. These generic algebraic
lemmas do not prove the unresolved source arithmetic characterization.
-/

theorem transfer_characterization {I A B : Type*}
    (old : I → A → Prop) (new : I → B → Prop) (target : I → Prop)
    (equiv : ∀ i, (∃ a, old i a) ↔ ∃ b, new i b)
    (source : ∀ i, (∃ a, old i a) ↔ target i) :
    ∀ i, (∃ b, new i b) ↔ target i := by
  intro i
  exact (equiv i).symm.trans (source i)

end QuarticOptimization
