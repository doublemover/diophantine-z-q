module
public import OriginalSieveCRTSurvivors318
public section
noncomputable section
namespace EulerBinomialError318
set_option maxHeartbeats 1000000

@[expose] def remainder (k : ℕ) (x : ℝ) : ℝ := (1-x)^k-1+(k:ℝ)*x

/-- Uniform quadratic remainder with an explicit constant, for all degrees. -/
theorem binomial_error (k : ℕ) (x : ℝ) (hx : 0≤x) (hx1 : x≤1) :
    0≤remainder k x ∧ remainder k x≤(k:ℝ)^2*x^2 := by
  induction k with
  | zero => simp [remainder]
  | succ k ih =>
    have he : remainder (k+1) x=(1-x)*remainder k x+(k:ℝ)*x^2 := by
      simp only [remainder,pow_succ,Nat.cast_add,Nat.cast_one]
      ring
    rw [he]
    have hprod0 : 0≤(1-x)*remainder k x := mul_nonneg (by linarith) ih.1
    have hprod1 : (1-x)*remainder k x≤remainder k x := by
      nlinarith [mul_nonneg hx ih.1]
    constructor
    · exact add_nonneg hprod0 (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg x))
    · push_cast
      nlinarith [sq_nonneg x, mul_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k) (sq_nonneg x)]

@[expose] def model (k : ℕ) (x e : ℝ) : ℝ := (1-x)^k*(1-e*x)^2

/-- The split/inert correction includes both character factors, not only
the k ordinary prime factors. -/
theorem model_error (k : ℕ) (x e : ℝ) (hx : 0≤x) (hx1 : x≤1)
    (he : e=1 ∨ e= -1) :
    |model k x e-(1-((k:ℝ)+2*e)*x)|≤(4*(k:ℝ)^2+3*(k:ℝ)+1)*x^2 := by
  obtain ⟨hR0,hR⟩ := binomial_error k x hx hx1
  have hB0 : 0≤(1-e*x)^2 := sq_nonneg _
  have hB : (1-e*x)^2≤4 := by rcases he with rfl|rfl <;> nlinarith
  have hRB0 : 0≤remainder k x*(1-e*x)^2 := mul_nonneg hR0 hB0
  have hRB : remainder k x*(1-e*x)^2≤4*(k:ℝ)^2*x^2 := by
    have hh := mul_le_mul hR hB hB0 (by positivity : 0≤(k:ℝ)^2*x^2)
    nlinarith
  have hx3 : 0≤x^3 := pow_nonneg hx 3
  have hx32 : x^3≤x^2 := by nlinarith [mul_nonneg (sq_nonneg x) (show 0≤1-x by linarith)]
  have hkx3 : (k:ℝ)*x^3≤(k:ℝ)*x^2 := mul_le_mul_of_nonneg_left hx32 (Nat.cast_nonneg k)
  have hkx30 : 0≤(k:ℝ)*x^3 := mul_nonneg (Nat.cast_nonneg k) hx3
  have hid : model k x e-(1-((k:ℝ)+2*e)*x)=
      remainder k x*(1-e*x)^2+(2*(k:ℝ)*e+1)*x^2-(k:ℝ)*x^3 := by
    rcases he with rfl|rfl <;> dsimp [model,remainder] <;> ring
  rw [hid,abs_le]
  rcases he with rfl|rfl
  all_goals constructor <;> nlinarith [sq_nonneg x,
    mul_nonneg (Nat.cast_nonneg k : (0:ℝ)≤k) (sq_nonneg x)]

/-- A uniform positive lower bound for the actual normalizing factor. -/
theorem model_lower (k : ℕ) (x e : ℝ) (hx : 0≤x) (hxhalf : x≤1/2)
    (hkx : (k:ℝ)*x≤1/2) (he : e=1 ∨ e= -1) :
    (1:ℝ)/8≤model k x e := by
  have hR := (binomial_error k x hx (by linarith)).1
  have hA : (1:ℝ)/2≤(1-x)^k := by dsimp [remainder] at hR; linarith
  have hB : (1:ℝ)/4≤(1-e*x)^2 := by rcases he with rfl|rfl <;> nlinarith
  dsimp [model]
  have hh := mul_le_mul hA hB (by norm_num : (0:ℝ)≤1/4) (by linarith : 0≤(1-x)^k)
  norm_num at hh ⊢
  exact hh

end EulerBinomialError318
