module
public import ActualTwoDescentLocalKummerWitness318
public section
noncomputable section
namespace ActualTwoDescentExceptionalLocalPoints318
open ActualTwoDescentLocalKummerWitness318 ActualTwoDescentTwoAdicSquare318
open ActualTwoDescentThreeAdicTorsion318
set_option maxHeartbeats 16000000

/-- The original beta17mod24 class has an ACTUAL local curve point at2,
not just a scalar square root or a formal identity class. -/
theorem actual_two_adic_kummer_point (β n : ℕ) (hβ : (β : ZMod 24)=17) :
    Nonempty (LocalKummerPoint (p:=2) β n) := by
  obtain ⟨r,hr⟩ := actual_two_adic_square_of_mod24 β (Or.inr hβ)
  have hβ0 : β ≠ 0 := by intro he; norm_num [he] at hβ
  have hr0 : r ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hr
    exact (Nat.cast_ne_zero.mpr hβ0) hr.symm
  exact actual_local_kummer_of_square β n r hr0 hr

/-- For either actual twist11mod12, the original beta class has an ACTUAL
local curve point at3 in precisely the retained Kummer coordinates. -/
theorem actual_three_adic_kummer_point (β n : ℕ) (hn0 : n ≠ 0)
    (hβ : (β : ZMod 24)=17) (hn : (n : ZMod 12)=11) :
    Nonempty (LocalKummerPoint (p:=3) β n) := by
  obtain ⟨r,hr,hclass⟩ := actual_beta_three_torsion β n hn0 hβ hn
  exact actual_local_kummer_of_first_torsion β n hn0 r hr hclass

/-- A literal real curve point and both nonzero Kummer square roots are
constructed from positivity, rather than merely recording a sign condition. -/
theorem actual_real_kummer_point (β n : ℕ) (hβ : 0 < β) :
    ∃ x y u v : ℝ, x ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
      y^2=x*(x-n)*(x+3*n) ∧ x+3*n=(β : ℝ)*u^2 ∧ x-n=v^2 := by
  have hβr : 0 < (β : ℝ) := by exact_mod_cast hβ
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hA : 0 < 4*(n : ℝ)+1 := by positivity
  let x : ℝ := n+1
  let y : ℝ := Real.sqrt ((n+1)*(4*n+1) : ℝ)
  let u : ℝ := Real.sqrt ((4*n+1 : ℝ)/β)
  refine ⟨x,y,u,1,by dsimp [x]; positivity,
    (Real.sqrt_pos.mpr (div_pos hA hβr)).ne',by norm_num,?_,?_,?_⟩
  · dsimp [x,y]
    rw [Real.sq_sqrt (by positivity)]
    ring
  · dsimp [x,u]
    rw [Real.sq_sqrt (div_pos hA hβr).le]
    field_simp [hβr.ne']
    <;> ring
  · dsimp [x]
    ring

end ActualTwoDescentExceptionalLocalPoints318
