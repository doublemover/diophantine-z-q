module
public import ActualOriginalDyadicPrimitiveCount318
public section
noncomputable section
namespace ActualOriginalDyadicFullRecurrence318
open QuadricCRTAssembly318 ActualFullLocalDensityRecurrence318 ActualSingularResidueCount318
open ActualOriginalDyadicPrimitiveCount318 ActualOriginalDyadicBaseCount318
set_option maxHeartbeats 28000000

/-- The full original singular fiber has32 lower-level choices, while
the actual primitive part is the just-constructed dyadic count. -/
theorem actual_original_dyadic_whole_recurrence (κ : ℤ) (hκ : (2:ℤ)∣κ)
    (hκ4 : ¬(2:ℤ)^2∣κ) (hκ8 : (κ:ZMod 8)=6) (e : ℕ) :
    count κ 2 (e+3)=2^(4*(e+3))+32*count κ 2 (e+1) := by
  have hh := actual_whole_quadric_split κ (2^(e+1)) 2
  have he : 2*(2^(e+1)*2)=2^(e+3) := by
    rw [show e+3=(e+1)+2 by omega,pow_add]
    ring
  rw [he,actual_primitive_all_dyadic_levels κ hκ hκ4 hκ8 e] at hh
  simpa only [count,show (2:ℕ)^5=32 by norm_num,mul_comm] using hh

theorem actual_original_dyadic_volume_recurrence (κ : ℤ) (hκ : (2:ℤ)∣κ)
    (hκ4 : ¬(2:ℤ)^2∣κ) (hκ8 : (κ:ZMod 8)=6) (e : ℕ) :
    volume κ 2 (e+3)=1+volume κ 2 (e+1)/8 := by
  unfold volume
  rw [actual_original_dyadic_whole_recurrence κ hκ hκ4 hκ8 e]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  have he : (2:ℚ)^(4*(e+3))=(2:ℚ)^(4*(e+1))*256 := by
    rw [show 4*(e+3)=4*(e+1)+8 by omega,pow_add]
    norm_num
  rw [he]
  field_simp
  <;> ring

lemma actual_original_dyadic_initial_volumes (κ : ℤ) (hκ2 : (κ:ZMod 2)=0)
    (hκ4 : (κ:ZMod 4)=2) : volume κ 2 1=1 ∧ volume κ 2 2=1 := by
  unfold volume
  rw [actual_original_dyadic_level_one κ hκ2,actual_original_dyadic_level_two κ hκ4]
  norm_num

end ActualOriginalDyadicFullRecurrence318
