module
public import Mathlib
public section
noncomputable section
namespace ActualTZLiteralFloorWindows318

@[expose] def height (τ : ℝ) (N : ℕ) : ℝ := τ*Real.sqrt (N:ℝ)
@[expose] def coarse (W : ℕ) (τ : ℝ) (N : ℕ) : ℕ := ⌊height τ N⌋₊/W-1
@[expose] def A (W : ℕ) (ρ : ℝ) : ℝ := (W:ℝ)^(1/ρ)
@[expose] def fine (W : ℕ) (τ ρ : ℝ) (N : ℕ) : ℕ := ⌊(coarse W τ N:ℝ)/A W ρ⌋₊

theorem coarse_bounds (W : ℕ) (hW : 0<W) (τ : ℝ) (hτ : 0≤τ) (N : ℕ) :
    height τ N/(W:ℝ)-3≤(coarse W τ N:ℝ) ∧
      (coarse W τ N:ℝ)≤height τ N/(W:ℝ) := by
  let T := ⌊height τ N⌋₊
  let q := T/W
  let r := T%W
  have hWr : (0:ℝ)<W := by exact_mod_cast hW
  have hT : (T:ℝ)≤height τ N := Nat.floor_le (by positivity)
  have hfloor : height τ N<(T:ℝ)+1 := Nat.lt_floor_add_one _
  have hQR : (r:ℝ)+(W:ℝ)*(q:ℝ)=T := by exact_mod_cast Nat.mod_add_div T W
  have hr : (r:ℝ)<W := by exact_mod_cast Nat.mod_lt T hW
  have hq₁ : (q:ℝ)≤height τ N/(W:ℝ) := (le_div_iff₀ hWr).2 (by
    have h : 0≤(r:ℝ) := by positivity
    nlinarith only [hT,hQR,h])
  have hq₂ : height τ N/(W:ℝ)≤(q:ℝ)+2 := (div_le_iff₀ hWr).2 (by
    have h : (1:ℝ)≤W := by exact_mod_cast (show 1≤W from hW)
    nlinarith only [hfloor,hQR,hr,h])
  have hdiff : (q:ℝ)≤(coarse W τ N:ℝ)+1 := by
    unfold coarse
    change (q:ℝ)≤((q-1:ℕ):ℝ)+1
    exact_mod_cast (show q≤q-1+1 by omega)
  have hqC : (coarse W τ N:ℝ)≤q := by
    unfold coarse
    exact_mod_cast Nat.sub_le q 1
  exact ⟨by linarith only [hq₂,hdiff],hqC.trans hq₁⟩

theorem A_one (W : ℕ) (hW : 0<W) (ρ : ℝ) (hρ : 0<ρ) : 1≤A W ρ :=
  Real.one_le_rpow (by exact_mod_cast (show 1≤W from hW)) (by positivity)

theorem fine_bounds (W : ℕ) (hW : 0<W) (τ ρ : ℝ) (hτ : 0≤τ) (hρ : 0<ρ) (N : ℕ) :
    height τ N/((W:ℝ)*A W ρ)-(3/A W ρ+1)≤(fine W τ ρ N:ℝ) ∧
      (fine W τ ρ N:ℝ)≤(coarse W τ N:ℝ)/A W ρ ∧
      fine W τ ρ N≤coarse W τ N := by
  have ha₁ := A_one W hW ρ hρ
  have ha := zero_lt_one.trans_le ha₁
  have hc := coarse_bounds W hW τ hτ N
  have hLower := div_le_div_of_nonneg_right hc.1 ha.le
  have hF := Nat.lt_floor_add_one ((coarse W τ N:ℝ)/A W ρ)
  have hU : (fine W τ ρ N:ℝ)≤(coarse W τ N:ℝ)/A W ρ :=
    Nat.floor_le (by positivity)
  have hC : (coarse W τ N:ℝ)/A W ρ≤(coarse W τ N:ℝ) := by
    exact div_le_self (by positivity) ha₁
  refine ⟨?_,hU,by exact_mod_cast hU.trans hC⟩
  rw [sub_div,div_div] at hLower
  change (coarse W τ N:ℝ)/A W ρ<(fine W τ ρ N:ℝ)+1 at hF
  linarith only [hLower,hF]

theorem fine_scaled (W D : ℕ) (hW : 0<W) (τ ρ : ℝ) (hτ : 0≤τ) (hρ : 0<ρ)
    (hD : (D:ℝ)≤1+1/ρ) (N : ℕ) :
    W^D*fine W τ ρ N≤W*coarse W τ N := by
  have h₁ : (1:ℝ)≤W := by exact_mod_cast (show 1≤W from hW)
  have hApos := zero_lt_one.trans_le (A_one W hW ρ hρ)
  have H : (W:ℝ)^D≤(W:ℝ)*A W ρ := by
    have hA : (W:ℝ)*A W ρ=(W:ℝ)^(1+1/ρ) := by
      rw [Real.rpow_add (zero_lt_one.trans_le h₁),Real.rpow_one,A]
    rw [←Real.rpow_natCast,hA]
    exact Real.rpow_le_rpow_of_exponent_le h₁ hD
  have hF : (A W ρ)*(fine W τ ρ N:ℝ)≤coarse W τ N := by
    have hh := (fine_bounds W hW τ ρ hτ hρ N).2.1
    rw [mul_comm]
    exact (le_div_iff₀ hApos).1 hh
  exact_mod_cast (show (W:ℝ)^D*(fine W τ ρ N:ℝ)≤(W:ℝ)*(coarse W τ N:ℝ) from
    (mul_le_mul_of_nonneg_right H (by positivity)).trans
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hF (by positivity)))

theorem coarse_scaled (W C : ℕ) (hW : 0<W) (τ : ℝ) (hτ : 0≤τ)
    (hC : 2*τ^2≤C) (N : ℕ) (hn : 0<N/W) :
    W*(coarse W τ N)^2≤C*(N/W) := by
  let n := N/W
  let M := coarse W τ N
  have hW' : (0:ℝ)<W := by exact_mod_cast hW
  have hn₁ : (1:ℝ)≤n := by exact_mod_cast (show 1≤n from hn)
  have hQR : ((N%W:ℕ):ℝ)+(W:ℝ)*(n:ℝ)=N := by exact_mod_cast Nat.mod_add_div N W
  have hr : ((N%W:ℕ):ℝ)<W := by exact_mod_cast Nat.mod_lt N hW
  have hN : (N:ℝ)≤2*(W:ℝ)*(n:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hn₁ hW'.le
    nlinarith only [hQR,hr,hh]
  have hM : (W:ℝ)*(M:ℝ)≤height τ N := by
    rw [mul_comm]
    exact (le_div_iff₀ hW').1 (coarse_bounds W hW τ hτ N).2
  have hS := pow_le_pow_left₀ (show (0:ℝ)≤(W:ℝ)*(M:ℝ) by positivity) hM 2
  have hSq : height τ N^2=τ^2*(N:ℝ) := by
    unfold height
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  rw [hSq] at hS
  have hh : (W:ℝ)*(W:ℝ)*(M:ℝ)^2≤((W:ℝ)*C)*(n:ℝ) := by
    calc
      _ ≤ τ^2*(N:ℝ) := by simpa only [mul_pow,pow_two,mul_assoc] using hS
      _ ≤ τ^2*(2*(W:ℝ)*(n:ℝ)) := mul_le_mul_of_nonneg_left hN (sq_nonneg _)
      _ = (W:ℝ)*(2*τ^2)*(n:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hW'.le) (by positivity)
  exact_mod_cast (show (W:ℝ)*(M:ℝ)^2≤(C:ℝ)*(n:ℝ) from
    (mul_le_mul_left hW').1 (by simpa only [mul_assoc] using hh))

end ActualTZLiteralFloorWindows318
