module
public import Mathlib
public section
noncomputable section
namespace ActualRayThinBudgetScalars318

/-- Exact scales on the historical row: no alternate dummy width,
and the step length is the actual quotient MINUS one. -/
theorem sizes (N T W : ℕ) (hW : 0 < W) (hN : 2000*W ≤ N)
    (hT : 200*W ≤ T) :
    let n := N/W
    let m := T/W-1
    let I := (3*n)/4+1-(5*n+7)/8
    (W:ℝ)*(n:ℝ) ≤ N ∧ (W:ℝ)*(m:ℝ) ≤ T ∧ I ≤ n ∧
    ((31:ℝ)/250)*(N:ℝ) ≤ (W:ℝ)*(I:ℝ) ∧
    ((99:ℝ)/100)*(T:ℝ) ≤ (W:ℝ)*(m:ℝ) := by
  let n := N/W
  let t := T/W
  let m := t-1
  let I := (3*n)/4+1-(5*n+7)/8
  have hn0 : 0 < n := by
    have hh : 1 ≤ N/W := (Nat.le_div_iff_mul_le hW).2 (by omega)
    omega
  have ht : 1 ≤ t := (Nat.le_div_iff_mul_le hW).2 (by omega)
  have hm : m+1 = t := by omega
  have hI : I ≤ n := by dsimp [I]; omega
  have hI' : n ≤ 8*I+8 := by dsimp [I]; omega
  have hWn : W*n ≤ N := by
    dsimp [n]
    rw [mul_comm]
    exact Nat.div_mul_le_self N W
  have hWt : W*t ≤ T := by
    dsimp [t]
    rw [mul_comm]
    exact Nat.div_mul_le_self T W
  have hWm : W*m ≤ T := (Nat.mul_le_mul_left W (Nat.sub_le _ _)).trans hWt
  have hN' : N ≤ W*n+W := by
    have hh : W*n+N%W = N := Nat.div_add_mod N W
    have hr := Nat.mod_lt N hW
    omega
  have hT' : T ≤ W*m+2*W := by
    have hh : W*t+T%W = T := Nat.div_add_mod T W
    have hr := Nat.mod_lt T hW
    have hAdd : W*t = W*m+W := by rw [←hm,Nat.mul_add,Nat.mul_one]
    rw [hAdd] at hh
    omega
  have hIr : (n:ℝ) ≤ 8*(I:ℝ)+8 := by exact_mod_cast hI'
  have hWr : (0:ℝ) ≤ W := by positivity
  have hIw := mul_le_mul_of_nonneg_left hIr hWr
  have hNw : (N:ℝ) ≤ (W:ℝ)*(n:ℝ)+(W:ℝ) := by exact_mod_cast hN'
  have hTw : (T:ℝ) ≤ (W:ℝ)*(m:ℝ)+2*(W:ℝ) := by exact_mod_cast hT'
  have hNbig : (2000:ℝ)*(W:ℝ) ≤ N := by exact_mod_cast hN
  have hTbig : (200:ℝ)*(W:ℝ) ≤ T := by exact_mod_cast hT
  change (W:ℝ)*(n:ℝ) ≤ N ∧ (W:ℝ)*(m:ℝ) ≤ T ∧ I ≤ n ∧
    ((31:ℝ)/250)*(N:ℝ) ≤ (W:ℝ)*(I:ℝ) ∧
    ((99:ℝ)/100)*(T:ℝ) ≤ (W:ℝ)*(m:ℝ)
  exact ⟨by exact_mod_cast hWn,by exact_mod_cast hWm,hI,
    by nlinarith only [hIw,hNw,hNbig,hWr],
    by linarith only [hTw,hTbig]⟩

/-- Finite exact allowances: one uniform majorant Z for the normalized
occupied row count is sufficient, and no extra field normalization is
inserted into either sum. -/
theorem allowances (N T W I m n k : ℕ) (S ε Z a C : ℝ)
    (hT : T ≤ N) (hWn : (W:ℝ)*(n:ℝ) ≤ N) (hWm : (W:ℝ)*(m:ℝ) ≤ T)
    (hI : I ≤ n) (hX : ((31:ℝ)/250)*(N:ℝ) ≤ (W:ℝ)*(I:ℝ))
    (hY : ((99:ℝ)/100)*(T:ℝ) ≤ (W:ℝ)*(m:ℝ))
    (hOcc : C ≤ Z*a*(W:ℝ)^2) (ha : 0 ≤ a) (hZ : 0 ≤ Z) (hε : 0 ≤ ε)
    (hErr : Z*(k:ℝ)*ε ≤ S/200) (hStrip : 6400*Z*(W:ℝ) ≤ S*(T:ℝ)) :
    ((3:ℝ)/25)*((N:ℝ)*(T:ℝ)) ≤ (I:ℝ)*(m:ℝ)*(W:ℝ)^2 ∧
    C*((k:ℝ)*(ε*(n:ℝ)*(m:ℝ))) ≤ a*(S*((N:ℝ)*(T:ℝ)))/200 ∧
    16*C*((I:ℝ)+(m:ℝ)) ≤ a*(S*((N:ℝ)*(T:ℝ)))/200 := by
  have hI' : (I:ℝ) ≤ n := by exact_mod_cast hI
  have hT' : (T:ℝ) ≤ N := by exact_mod_cast hT
  have hNT : 0 ≤ (N:ℝ)*(T:ℝ) := by positivity
  have hnm : (W:ℝ)*(n:ℝ)*((W:ℝ)*(m:ℝ)) ≤ (N:ℝ)*(T:ℝ) :=
    mul_le_mul hWn hWm (by positivity) (by positivity)
  have hArea := mul_le_mul hX hY (by positivity : 0 ≤ ((99:ℝ)/100)*(T:ℝ))
    (by positivity : 0 ≤ (W:ℝ)*(I:ℝ))
  have hWidth : (W:ℝ)*((I:ℝ)+(m:ℝ)) ≤ 2*(N:ℝ) := by
    rw [mul_add]
    have h := mul_le_mul_of_nonneg_left hI' (show 0 ≤ (W:ℝ) by positivity)
    linarith only [h,hWn,hWm,hT']
  have hPair := mul_le_mul_of_nonneg_left hnm (show 0 ≤ a*(Z*(k:ℝ)*ε) from
    mul_nonneg ha (by positivity))
  have hScale := mul_le_mul_of_nonneg_right hErr (show 0 ≤ a*((N:ℝ)*(T:ℝ)) from
    mul_nonneg ha hNT)
  have hSpace := mul_le_mul_of_nonneg_right hStrip (show 0 ≤ a*(N:ℝ)/200 by positivity)
  have hUpper1 := mul_le_mul_of_nonneg_right hOcc
    (show 0 ≤ (k:ℝ)*(ε*(n:ℝ)*(m:ℝ)) by positivity)
  have hUpper2 := mul_le_mul_of_nonneg_right hOcc (show 0 ≤ 16*((I:ℝ)+(m:ℝ)) by positivity)
  have hWidth' := mul_le_mul_of_nonneg_left hWidth (show 0 ≤ 16*Z*a*(W:ℝ) by positivity)
  refine ⟨by nlinarith only [hArea,hNT],?_,?_⟩
  · nlinarith only [hUpper1,hPair,hScale]
  · nlinarith only [hUpper2,hWidth',hSpace]

end ActualRayThinBudgetScalars318
