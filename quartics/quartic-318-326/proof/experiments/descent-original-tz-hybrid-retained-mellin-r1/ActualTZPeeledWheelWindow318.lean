module
public import ActualTZLiteralOffsetMajorants318
public section
noncomputable section
namespace ActualTZPeeledWheelWindow318
open ActualTZLiteralOffsetMajorants318 ActualTZLiteralProbeSpecialization318
open ActualTZLiteralTerminalLift318 ActualTZJointPolynomialForms318

variable {m a b j : ℕ}

/-- This is the exact source-shape consumption. Fixed-y sufficiently
large n absorbs the fixed pure constant. The genuine fine/coarse
scale and small pure-coarse coefficients give a bound C*n with C
independent of the selected y, in contrast to a uniform W^D knob. -/
theorem peeled_wrap_bound (S : Terminal m a b) (u : Site a b j)
    (W B C M H N A T : ℤ) (D : ℕ)
    (hW : 0≤W) (hB : 0≤B) (hC : 1≤C) (hM : 0≤M) (hH : 1≤H) (hN : 0≤N)
    (hMH : M≤H) (bounds : Bounds S A T)
    (hA : A≤B*W^D) (hT : T≤B*W)
    (hPure : W^D≤N) (hFine : W^D*M≤W*H) (hCoarse : W*H^2≤C*N)
    (h : Fin m→ℤ) (k : Bool→Fin a→ℤ) (c : Fin j→ℤ)
    (hh : ∀ i,|h i|≤M) (hk : ∀ e i,|k e i|≤M) (hc : ∀ i,|c i|≤H) :
    |eOffset S u h k c|≤((cap m a:ℤ)*B*C)*N := by
  let U := B*(C*N)
  have hC0 : 0≤C := zero_le_one.trans hC
  have hH0 : 0≤H := zero_le_one.trans hH
  have hN' : N≤C*N := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hN
  have kA : A≤U := hA.trans (mul_le_mul_of_nonneg_left (hPure.trans hN') hB)
  have kF : A*M*H≤U := by
    calc
      _ ≤ (B*W^D)*M*H := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hA hM) hH0
      _ = B*(W^D*M)*H := by ring
      _ ≤ B*(W*H)*H := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hFine hB) hH0
      _ = B*(W*H^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCoarse hB
  have kT : T*H^2≤U := by
    calc
      _ ≤ (B*W)*H^2 := mul_le_mul_of_nonneg_right hT (sq_nonneg _)
      _ = B*(W*H^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCoarse hB
  have R := offset_bound S u A T M H U bounds hM hH hMH kA kF kT h k c hh hk hc
  exact R.trans_eq (by dsimp only [U]; ring)

/-- The same exact formulas give effective H-dependent sizes for
all tiny integer diagnostic probe values (basis sums use ≤2). -/
theorem probe_offset_bound (S : Terminal m a b) (u : Site a b j)
    (A T : ℤ) (bounds : Bounds S A T) (hT : T≤A)
    (h : Fin m→ℤ) (k : Bool→Fin a→ℤ) (c : Fin j→ℤ)
    (hh : ∀ i,|h i|≤2) (hk : ∀ e i,|k e i|≤2) (hc : ∀ i,|c i|≤2) :
    |eOffset S u h k c|≤(cap m a:ℤ)*(4*A) := by
  have hA : A≤4*A := by linarith only [bounds.a0]
  have kF : A*2*2≤4*A := (show A*2*2=4*A by ring).le
  have kT : T*2^2≤4*A := by linarith only [hT]
  exact offset_bound S u A T 2 2 (4*A) bounds (by norm_num) (by norm_num) le_rfl
    hA kF kT h k c hh hk hc

end ActualTZPeeledWheelWindow318
