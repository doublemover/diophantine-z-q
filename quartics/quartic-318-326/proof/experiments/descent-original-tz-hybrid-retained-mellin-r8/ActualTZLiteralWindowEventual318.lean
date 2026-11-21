module
public import ActualTZLiteralFloorWindows318
public section
noncomputable section
namespace ActualTZLiteralWindowEventual318
open Filter
open scoped Topology
open ActualTZLiteralFloorWindows318

theorem natural_growth (W : ℕ) (hW : 0<W) :
    Tendsto (fun N : ℕ=>N/W) atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [eventually_ge_atTop (m*W)] with N hN
  exact (Nat.le_div_iff_mul_le hW).2 hN

theorem logarithmic_growth (W : ℕ) (hW : 0<W) (ρ : ℝ) (hρ : 0<ρ) :
    Tendsto (fun N : ℕ=>Real.log (((N/W:ℕ):ℝ)^ρ)) atTop atTop := by
  have hN := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ=>(n:ℝ)) atTop atTop).comp
    (natural_growth W hW)
  have hP := (_root_.tendsto_rpow_atTop hρ).comp hN
  exact Real.tendsto_log_atTop.comp hP

/-- Quantifier order: C after τ but before W and ρ; d after fixing
the physical cut's W. Old floors, including the subtract-one, are
unchanged. This gives both true powers used by the collision/CRT
tail and signed chart. -/
theorem fixed_windows (τ : ℝ) (hτ : 0<τ) :
    ∃ C : ℕ,1≤C ∧ 2*τ^2≤(C:ℝ) ∧
      ∀ (W D : ℕ) (ρ : ℝ),0<W→0<ρ→(D:ℝ)≤1+1/ρ→
        ∃ d>0,∃ N₀ : ℕ,∀ N≥N₀,
          0<N/W ∧ 0<fine W τ ρ N ∧ fine W τ ρ N≤coarse W τ N ∧
          W*(N/W)≤N ∧ W^D≤N/W ∧ W^D*fine W τ ρ N≤W*coarse W τ N ∧
          W*(coarse W τ N)^2≤C*(N/W) ∧ d*(N:ℝ)^((1:ℝ)/2)≤fine W τ ρ N := by
  obtain ⟨C,hC⟩ := exists_nat_gt (max (1:ℝ) (2*τ^2))
  have hCone : (1:ℝ)≤C := (le_max_left _ _).trans hC.le
  have hCτ : 2*τ^2≤(C:ℝ) := (le_max_right _ _).trans hC.le
  refine ⟨C,by exact_mod_cast hCone,hCτ,?_⟩
  intro W D ρ hW hρ hD
  let d := τ/(2*(W:ℝ)*A W ρ)
  have hWr : (0:ℝ)<W := by exact_mod_cast hW
  have hA := zero_lt_one.trans_le (A_one W hW ρ hρ)
  have hd : 0<d := by unfold d; positivity
  have he : τ/((W:ℝ)*A W ρ)=2*d := by
    unfold d
    field_simp [hWr.ne',hA.ne'] <;> ring
  let B := 3/A W ρ+1
  have hB : 0≤B := by unfold B; positivity
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt ((B/d)^2)
  refine ⟨d,hd,max (W^D*W) N₁,?_⟩
  intro N hN
  have hP : W^D≤N/W := (Nat.le_div_iff_mul_le hW).2 ((le_max_left _ _).trans hN)
  have hp : 0<W^D := pow_pos hW _
  have hn := hp.trans_le hP
  have hS : W*(N/W)≤N := by
    have H := Nat.mod_add_div N W
    omega
  have hR : (0:ℝ)<N := by
    have hh : 0<N := (mul_pos hW hn).trans_le hS
    exact_mod_cast hh
  have hQ : (B/d)^2≤(N:ℝ) := hN₁.le.trans (by exact_mod_cast (le_max_right (W^D*W) N₁).trans hN)
  have hSq := Real.sqrt_le_sqrt hQ
  rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (div_nonneg hB hd.le)] at hSq
  have hBB : B≤d*Real.sqrt (N:ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hd).1 hSq
  have hL := (fine_bounds W hW τ ρ hτ.le hρ N).1
  have hhr : height τ N/((W:ℝ)*A W ρ)=2*d*Real.sqrt (N:ℝ) := by
    unfold height
    rw [←he]
    field_simp [hWr.ne',hA.ne'] <;> ring
  rw [hhr] at hL
  change 2*d*Real.sqrt (N:ℝ)-B≤_ at hL
  have hLower : d*Real.sqrt (N:ℝ)≤(fine W τ ρ N:ℝ) := by linarith only [hL,hBB]
  have hPos : 0<fine W τ ρ N := by
    exact_mod_cast (mul_pos hd (Real.sqrt_pos.2 hR)).trans_le hLower
  refine ⟨hn,hPos,(fine_bounds W hW τ ρ hτ.le hρ N).2.2,hS,hP,
    fine_scaled W D hW τ ρ hτ.le hρ hD N,coarse_scaled W C hW τ hτ.le hCτ N hn,?_⟩
  simpa only [Real.sqrt_eq_rpow] using hLower

end ActualTZLiteralWindowEventual318
