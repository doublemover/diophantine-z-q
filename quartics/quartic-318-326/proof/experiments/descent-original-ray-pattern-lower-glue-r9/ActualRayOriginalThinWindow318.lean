module
public import ActualRayOccupiedLower318
public import ActualRayOriginalThinWindowScalar318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualRayOriginalThinWindow318

open OriginalInteriorTelescoping318 ActualRayOccupiedLower318 ActualRayLiteralInteriorWeight318
open ActualRayOriginalThinWindowScalar318

/-- Literal original dummy support implies the physical thin box.
The same proof supplies lower mass and the selected sieve geometry. -/
theorem on_actual_row (F : Family) (y N : ℕ) {r : Row} (hr : r ∈ F.rows y N)
    (hW : 0 < wheel y) (hN : 16*wheel y ≤ N)
    (hK : |(F.K:ℝ)|*F.tau^2 ≤ 1/32)
    (hCi : ∀ i < F.k, |((F.ci i-F.K:ℤ):ℝ)|*F.tau^2 ≤ 1/32)
    (z : Dom r) (hz : dummy r z = 1) :
    InThinBox r N (cutoffT F N) (baseIndex r z) (stepIndex r z) := by
  obtain ⟨b,c,hb,hbw,hc,hcw,hEq,_⟩ := hr
  let W := wheel y
  let n := N/W
  let T := cutoffT F N
  let x := z.1.val+1
  let m := z.2.val+1
  have hwr : r.W = W := by rw [hEq] <;> rfl
  have hnr : r.n = n := by rw [hEq] <;> rfl
  have hmr : r.M = T/W-1 := by rw [hEq] <;> rfl
  have hbr : r.b = b := by rw [hEq] <;> rfl
  have hcr : r.c = c := by rw [hEq] <;> rfl
  have hkr : r.k = F.k := by rw [hEq] <;> rfl
  have hKr : r.K = F.K := by rw [hEq] <;> rfl
  have hCir : r.ci = F.ci := by rw [hEq] <;> rfl
  have hx : 5*n ≤ 8*x ∧ 4*x ≤ 3*n := by
    unfold dummy at hz
    rw [hnr] at hz
    change (if 5*n ≤ 8*x ∧ 4*x ≤ 3*n then (1:ℝ) else 0)=1 at hz
    split_ifs at hz with h
    · exact h
    · norm_num at hz
  have hU : physicalU r (baseIndex r z) = (W:ℤ)*(x:ℤ)+b := by
    simp only [physicalU,baseIndex,hwr,hbr,x,Nat.cast_add,Nat.cast_one]
  have hV : physicalV r (stepIndex r z) = (W:ℤ)*(m:ℤ)+c := by
    simp only [physicalV,stepIndex,hwr,hcr,m,Nat.cast_add,Nat.cast_one]
  have hcN : c.toNat < W := by
    have h : ((c.toNat:ℕ):ℤ) < (W:ℤ) := by rw [Int.toNat_of_nonneg hc]; exact hcw
    exact_mod_cast h
  have hm : m ≤ T/W-1 := by rw [←hmr]; exact Nat.succ_le_of_lt z.2.isLt
  have hStep := step_upper W T m c.toNat hW hm (by unfold m; omega) hcN
  have hVbounds : (1:ℤ) ≤ physicalV r (stepIndex r z) ∧ physicalV r (stepIndex r z) ≤ (T:ℤ) := by
    rw [hV]
    have hV' : (1:ℤ) ≤ ((W*m+c.toNat:ℕ):ℤ) ∧ ((W*m+c.toNat:ℕ):ℤ) ≤ (T:ℤ) := by
      constructor
      · exact_mod_cast hStep.1
      · exact_mod_cast hStep.2
    simpa only [Nat.cast_add,Nat.cast_mul,Int.toNat_of_nonneg hc] using hV'
  have hWN : W*n ≤ N := by have h := Nat.mod_add_div N W; omega
  have hNW : N ≤ W*n+W := by
    have h := Nat.mod_add_div N W
    have hm' := Nat.mod_lt N hW
    omega
  have hx₀ : (5:ℝ)*n ≤ 8*(x:ℝ) := by exact_mod_cast hx.1
  have hx₁ : (4:ℝ)*x ≤ 3*(n:ℝ) := by exact_mod_cast hx.2
  have hm₀ := mul_le_mul_of_nonneg_left hx₀ (show (0:ℝ) ≤ W by positivity)
  have hm₁ := mul_le_mul_of_nonneg_left hx₁ (show (0:ℝ) ≤ W by positivity)
  have hWN' : (W:ℝ)*(n:ℝ) ≤ N := by exact_mod_cast hWN
  have hNW' : (N:ℝ) ≤ (W:ℝ)*(n:ℝ)+(W:ℝ) := by exact_mod_cast hNW
  have hb' : (0:ℝ) ≤ b := by exact_mod_cast (show (0:ℤ) ≤ b by omega)
  have hbw' : (b:ℝ) ≤ W := by exact_mod_cast hbw
  have hU' : (physicalU r (baseIndex r z):ℝ)=(W:ℝ)*(x:ℝ)+(b:ℝ) := by
    exact_mod_cast hU
  have hV' : (0:ℝ) ≤ physicalV r (stepIndex r z) := by exact_mod_cast (zero_le_one.trans hVbounds.1)
  have hT : (T:ℝ) ≤ F.tau*Real.sqrt (N:ℝ) := Nat.floor_le (by positivity)
  have hTV : (physicalV r (stepIndex r z):ℝ) ≤ (T:ℝ) := by exact_mod_cast hVbounds.2
  have hW' : (16:ℝ)*(W:ℝ) ≤ N := by exact_mod_cast hN
  have hBoxD (D : ℤ) (hD : |(D:ℝ)|*F.tau^2 ≤ 1/32) :
      (N:ℤ) ≤ 2*(physicalU r (baseIndex r z) + D*(physicalV r (stepIndex r z))^2) ∧
      physicalU r (baseIndex r z) + D*(physicalV r (stepIndex r z))^2 ≤ (N:ℤ) := by
    obtain ⟨hLo,hHi⟩ := bounds (N:ℝ) (W:ℝ) (physicalU r (baseIndex r z):ℝ)
      (physicalV r (stepIndex r z):ℝ) (Real.sqrt (N:ℝ)) F.tau (D:ℝ)
      (by positivity) hW' hV' (hTV.trans hT) (by positivity) (Real.sq_sqrt (by positivity))
      ⟨by nlinarith only [hm₀,hNW',hU',hb'],by nlinarith only [hm₁,hWN',hU',hbw']⟩ hD
    exact ⟨by exact_mod_cast hLo,by exact_mod_cast hHi⟩
  have hBase := hBoxD (-r.K) (by simpa only [Int.cast_neg,abs_neg,hKr] using hK)
  change (N:ℤ) ≤ 2*physicalUOriginal r (baseIndex r z) (stepIndex r z) ∧
    physicalUOriginal r (baseIndex r z) (stepIndex r z) ≤ (N:ℤ) ∧
    1 ≤ physicalV r (stepIndex r z) ∧ physicalV r (stepIndex r z) ≤ (T:ℤ) ∧ _
  simp only [physicalUOriginal,neg_mul,←sub_eq_add_neg] at hBase ⊢
  refine ⟨hBase.1,hBase.2,hVbounds.1,hVbounds.2,?_⟩
  intro i hi
  rw [physical_shear]
  exact hBoxD (d r i) (by simpa only [d,hCir,hKr] using hCi i (hkr ▸ hi))

theorem on_occupied (F : Family) (y N : ℕ) (hW : 0 < wheel y) (hN : 16*wheel y ≤ N)
    (hK : |(F.K:ℝ)|*F.tau^2 ≤ 1/32)
    (hCi : ∀ i < F.k, |((F.ci i-F.K:ℤ):ℝ)|*F.tau^2 ≤ 1/32) :
    ∀ j ∈ occupied F y N, ∀ z : Dom (rowAt F y N j),
      dummy (rowAt F y N j) z = 1 →
      InThinBox (rowAt F y N j) N (cutoffT F N)
        (baseIndex (rowAt F y N j) z) (stepIndex (rowAt F y N j) z) := by
  intro j hj z hz
  exact on_actual_row F y N (occupied_mem_actual F y N j hj) hW hN hK hCi z hz

end ActualRayOriginalThinWindow318
