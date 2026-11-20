module
public import NormalizedPolePoints318
public import Mathlib.Tactic.NormNum
public section

namespace OriginalSelected323RationalPointPair318

/-- The single concrete original selected cubic, not an all-integer source. -/
def x : ℚ := 9226753553 / 5973136
def y : ℚ := 1005467646233175 / 14598344384
def r : ℚ := 23297 / 2444
def u : ℚ := 29719 / 2444
def v : ℚ := 85425 / 2444

theorem ordered_mark :
    x > 0 ∧ y > 0 ∧ r > 0 ∧ u > 0 ∧ v > 0 ∧
    x = 17*r^2 ∧ x+3*323 = 17*u^2 ∧ x-323 = v^2 ∧
    y = 17*r*u*v ∧ y^2 = x*(x-323)*(x+3*323) := by
  norm_num [x,y,r,u,v]

/-- Concrete eligible-shaped datum; no equality with a prepared table row
is claimed. Its selected squarefree companion parameter is theta = 1. -/
def c : ℚ := 204 / 613
def e : ℚ := 611 / 613
def b : ℚ := c^2
def s : ℚ := (17*b)*e
def λ : ℚ := c/r
def T : ℚ := 323*λ^2
def y₁ : ℚ := y*λ^3
def y₂ : ℚ := y*(λ*s)^3

theorem scale_data :
    0 < b ∧ b < 17 ∧ 0 < c ∧ 0 < e ∧ 0 < s ∧ 0 < λ ∧ 0 < T ∧
    0 < y₁ ∧ 0 < y₂ ∧ 17*b = 17*c^2 ∧
    1-b/17 = e^2 ∧ (17*b)^2*(1-b/17) = s^2 := by
  norm_num [b,c,e,s,λ,T,y₁,y₂,y,r]

/-- The actual two-pole-equations data at this same numerical b. One
rational Kummer point is reused because the second selected curve is
literally E_(323*1); its homogeneity scale, and hence its ordinate, changes. -/
def pointPair : NormalizedPolePoints318.PointPair b where
  parameter := T
  s := s
  y₁ := y₁
  y₂ := y₂
  s_ne := by norm_num [s,b,c,e]
  first := by norm_num [T,y₁,y,λ,r,b,c]
  second := by norm_num [T,y₂,y,λ,r,b,c,s,e]

/-- Direct output ABI of the original pole-extension consumer. -/
noncomputable def certificate : NormalizedPolePoints318.Certificate b :=
  pointPair.certificate (ne_of_gt scale_data.1)

theorem has_point_pair : Nonempty (NormalizedPolePoints318.PointPair b) :=
  ⟨pointPair⟩

end OriginalSelected323RationalPointPair318

#print axioms OriginalSelected323RationalPointPair318.ordered_mark
#print axioms OriginalSelected323RationalPointPair318.has_point_pair
#print axioms OriginalSelected323RationalPointPair318.certificate
