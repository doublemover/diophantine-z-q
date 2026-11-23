module
public import Mathlib.Tactic
public section
namespace LinearObservationReconstruction318

/-- Slots are the merged integer slopes, plus the distinct denominator slot.
These are the two integer coordinates of each physical rational prime key. -/
abbrev Slot := Option ℤ
abbrev Key := ℤ × ℤ

def du : Slot → ℤ
  | none => 0
  | some _ => 1

def dq (Q : ℤ) : Slot → ℤ
  | none => 1
  | some k => k*Q^2

def value (Q : ℤ) (i : Slot) (x : Key) := du i*x.1 + dq Q i*x.2
def det (Q : ℤ) (i j : Slot) := du i*dq Q j - du j*dq Q i

@[simp] theorem value_none (Q : ℤ) (x : Key) : value Q none x = x.2 := by simp [value,du,dq]
@[simp] theorem value_some (Q k : ℤ) (x : Key) : value Q (some k) x = x.1+k*Q^2*x.2 := by
  simp [value,du,dq]
theorem det_ne {Q : ℤ} (hQ : Q ≠ 0) {i j : Slot} (hne : i ≠ j) : det Q i j ≠ 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hne rfl).elim
    | some l => simp [det,du,dq]
  | some k =>
    cases j with
    | none => simp [det,du,dq]
    | some l =>
      have hkl : l ≠ k := by rintro rfl; exact hne rfl
      change 1*(l*Q^2) - 1*(k*Q^2) ≠ 0
      rw [one_mul,one_mul,← sub_mul]
      exact mul_ne_zero (sub_ne_zero.mpr hkl) (pow_ne_zero _ hQ)

theorem cramer (Q : ℤ) (i j : Slot) (x : Key) :
    value Q i x*dq Q j - value Q j x*dq Q i = det Q i j*x.1 ∧
      du i*value Q j x - du j*value Q i x = det Q i j*x.2 := by
  unfold value det
  constructor <;> ring

/-- Needed for an A4 sieve on two observed Gaussian norms. A pair of distinct
norm observations pins down the original two-dimensional key; it does not
require any integrality conditions on a rational matrix inverse. -/
theorem injective_pair {Q : ℤ} (hQ : Q ≠ 0) {i j : Slot} (hne : i ≠ j) :
    Function.Injective (fun x : Key => (value Q i x, value Q j x)) := by
  intro x y h
  have h1 : value Q i x = value Q i y := congrArg Prod.fst h
  have h2 : value Q j x = value Q j y := congrArg Prod.snd h
  obtain ⟨cx,dx⟩ := cramer Q i j x
  obtain ⟨cy,dy⟩ := cramer Q i j y
  rw [h1,h2] at cx dx
  have e₁ : det Q i j * (x.1-y.1) = 0 := by rw [mul_sub,← cx,← cy,sub_self]
  have e₂ : det Q i j * (x.2-y.2) = 0 := by rw [mul_sub,← dx,← dy,sub_self]
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp e₁).resolve_left (det_ne hQ hne)))
    (sub_eq_zero.mp ((mul_eq_zero.mp e₂).resolve_left (det_ne hQ hne)))

/-- The four-dimensional Gaussian box can majorize a set of rational keys
by choosing any representation for two observed norms. Multiplicities or
a canonical choice of generators are *not* needed for this upper bound. -/
theorem injective_coordinates {α : Type*} {Q : ℤ} (hQ : Q ≠ 0)
    {i j : Slot} (hne : i ≠ j) (rows : α → Key) (hr : Function.Injective rows)
    (g : α → (ℤ × ℤ) × (ℤ × ℤ))
    (hi : ∀ z, (g z).1.1^2 + (g z).1.2^2 = value Q i (rows z))
    (hj : ∀ z, (g z).2.1^2 + (g z).2.2^2 = value Q j (rows z)) :
    Function.Injective g := by
  intro x y h
  apply hr
  apply injective_pair hQ hne
  apply Prod.ext
  · change value Q i (rows x) = value Q i (rows y)
    rw [← hi x,← hi y,h]
  · change value Q j (rows x) = value Q j (rows y)
    rw [← hj x,← hj y,h]

/-- A diagonal translated-norm accident uses a *different companion slot*
only for encoding its original key. It still tests the same generator twice. -/
theorem companion (k₀ : ℤ) (i : Slot) : ∃ j : Slot, i ≠ j := by
  cases i with
  | none => exact ⟨some k₀,by simp⟩
  | some k => exact ⟨none,by simp⟩

/-- At a fixed value of a contact form, q determines u: this is the fibre
bound used when removing non-prime prime-power values from FT weights. -/
theorem fixed_contact {Q k : ℤ} {x y : Key} (h : value Q (some k) x = value Q (some k) y)
    (hq : x.2=y.2) : x=y := by
  simp only [value_some,hq] at h
  exact Prod.ext (add_right_cancel h) hq

theorem fixed_denominator {Q : ℤ} {x y : Key} (h : value Q none x = value Q none y)
    (hu : x.1=y.1) : x=y := Prod.ext hu (by simpa only [value_none] using h)

end LinearObservationReconstruction318
