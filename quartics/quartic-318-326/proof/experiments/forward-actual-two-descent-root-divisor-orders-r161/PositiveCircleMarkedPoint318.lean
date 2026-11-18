module
public import NormalizedPolePoints318
public section
namespace PositiveCircleMarkedPoint318

/-- The actual two nonzero roots of the matching Jacobian, before square scaling. -/
def rootOne (β θ k : ℚ) : ℚ := β * (θ * (1 - β*k^2)) * (25*(β*k^2)-9)
def rootTwo (β θ k : ℚ) : ℚ := 16 * β * (θ * (1 - β*k^2)) * (β*k^2)

/-- A rational point with explicit ordered full Kummer representatives.
This record does not assert infinite order. -/
structure CompanionPoint (β θ k : ℚ) where
  x : ℚ
  y : ℚ
  u : ℚ
  v : ℚ
  w : ℚ
  y_ne : y ≠ 0
  first : x = β*u^2
  second : x - rootOne β θ k = v^2
  third : x - rootTwo β θ k = β*w^2
  equation : y^2 = x * (x - rootOne β θ k) * (x - rootTwo β θ k)

/-- Literal companion point on the actual unscaled model, not the required (1,β,β) cover. -/
def ofCoefficient (β θ k q : ℚ) (hβ : β ≠ 0) (hk : k ≠ 0) (hq : q ≠ 0)
    (hc : θ*(1 - β*k^2) = β*q^2) : CompanionPoint β θ k where
  x := (β*q)^2 * (25*(β*k^2))
  y := (β*q)^3 * (45*(β*k^2))
  u := 5*(β*q)*k
  v := 3*(β*q)
  w := 3*(β*q)*k
  y_ne := mul_ne_zero (pow_ne_zero _ (mul_ne_zero hβ hq))
    (mul_ne_zero (by norm_num) (mul_ne_zero hβ (pow_ne_zero _ hk)))
  first := by ring
  second := by unfold rootOne; rw [hc]; ring
  third := by unfold rootTwo; rw [hc]; ring
  equation := by unfold rootOne rootTwo; rw [hc]; ring

/-- Exact coefficient produced from the given scale r and a rational sum-of-squares choice. -/
theorem selectCoefficient (β θ r z u v : ℚ) (hr : 1 - β*r^2 = θ*z^2)
    (hu : 1 - β*u^2 = β*v^2) (hd : 1 + β*r*u ≠ 0) :
    θ * (1 - β*((r+u)/(1+β*r*u))^2) =
      β*((θ*z*v)/(1+β*r*u))^2 := by
  have hm : 1 - β*((r+u)/(1+β*r*u))^2 =
      ((1-β*r^2)*(1-β*u^2))/(1+β*r*u)^2 := by
    field_simp [hd] <;> ring
  rw [hm,hr,hu]
  field_simp [hd] <;> ring

theorem sumOfSquaresInput (β s t : ℚ) (hβ : β ≠ 0) (hs : s^2+t^2=β) :
    1 - β*(s/β)^2 = β*(t/β)^2 := by
  field_simp [hβ] <;> nlinarith [congrArg (fun a : ℚ => β*a) hs]

/-- Concrete non-indexed test pole 55² - 17·12² = 577. -/
def testPole : ℚ := ((204:ℚ)/55)^2

/-- The same two original matched ordinates arising from the rank-four and rank-two
Jacobian controls. This consumes the actual imported PointPair, not a copy. -/
def testPair : NormalizedPolePoints318.PointPair testPole where
  parameter := 5659776/75625
  s := 2749943664/44089375
  y₁ := 17174590272/4159375
  y₂ := 1762046034616528632746832160702070784/2851805428717604473876953125
  s_ne := by norm_num
  first := by norm_num [testPole]
  second := by norm_num [testPole]

theorem testPair_nonzero : testPair.y₁ ≠ 0 ∧ testPair.y₂ ≠ 0 := by
  norm_num [testPair]

noncomputable def testCertificate : NormalizedPolePoints318.Certificate testPole :=
  NormalizedPolePoints318.PointPair.certificate (by norm_num [testPole]) testPair

end PositiveCircleMarkedPoint318
