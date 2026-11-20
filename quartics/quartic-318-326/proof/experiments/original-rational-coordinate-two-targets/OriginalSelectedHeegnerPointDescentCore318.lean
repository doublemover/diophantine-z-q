module
public import ActualTwoDescentGaloisFixedRational318
public import Mathlib.GroupTheory.OrderOfElement
public section
noncomputable section
namespace OriginalSelectedHeegnerPointDescent318
open ActualTwoDescentEllipticModel318
open ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentGaloisFixedRational318
local instance : DecidableEq Qbar := Classical.decEq _
/-- The actual marked geometric point multiplied by the specified positive
integer descends to both rational coordinates, without losing infinite order. -/
theorem rational_nontorsion_of_killed_translates (n : ℚ) (hn : n ≠ 0)
    (P : Point (algebraMap ℚ Qbar n)) (m : ℕ) (hm : 0 < m)
    (hP : ¬ IsOfFinAddOrder P)
    (htrans : ∀ σ : GalQ, m • (galoisPointHom σ n hn P - P) = 0) :
    ∃ R : Point n, rationalPointMap n hn R = m • P ∧ ¬ IsOfFinAddOrder R := by
  have hfix (σ : GalQ) : galoisPointHom σ n hn (m • P) = m • P := by
    rw [map_nsmul]
    exact sub_eq_zero.mp (by simpa only [nsmul_sub] using htrans σ)
  obtain ⟨R, hR⟩ := actual_fixed_point_rational n hn (m • P) hfix
  refine ⟨R, hR, ?_⟩
  intro hT
  obtain ⟨k, hk, hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hT
  have hmap : k • rationalPointMap n hn R = 0 := by
    rw [← map_nsmul, hkill, map_zero]
  rw [hR] at hmap
  exact hP (isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    ⟨k * m, Nat.mul_pos hk hm, by simpa only [mul_nsmul] using hmap⟩)

end OriginalSelectedHeegnerPointDescent318
