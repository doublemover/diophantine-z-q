module
public import FixedAnchorNormDepths318
public section
noncomputable section
namespace ActualAnchorRatio318
open FixedDetectorScales318 ScalarIndexValuations318 FixedAnchorNormDepths318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Literal physical-anchor ratio after dividing by its nonzero scale3^N. -/
@[expose] def ratio (labels : Fin 4 → ℤ) (N : ℕ) : ℚ :=
  4096*normProduct labels+ActualScalarRoot318.inverseNorm (labels 1)/(3:ℚ)^N

lemma physical_identity (labels : Fin 4 → ℤ) (N : ℕ) :
    4096*normProduct labels*(3:ℚ)^N+ActualScalarRoot318.inverseNorm (labels 1)=
      (3:ℚ)^N*ratio labels N := by
  unfold ratio
  field_simp
  ring

/-- Actual odd labels and sufficient translated3-depth make the literal
normalized anchor a2-adic unit and3-adically integral. -/
theorem local_depths (labels : Fin 4 → ℤ) (hn : ∀ j, Odd (labels j))
    (hn1 : labels 1≠1) (N : ℕ)
    (hdeep : (N:ℤ)≤2+2*(padicValInt 3 (labels 1-1):ℤ)) :
    ratio labels N≠0 ∧ padicValRat 2 (ratio labels N)=0 ∧
      0≤padicValRat 3 (ratio labels N) := by
  have hn0 := odd_nonzero (labels 1) (hn 1)
  have hI : ActualScalarRoot318.inverseNorm (labels 1)≠0 :=
    inv_ne_zero (ActualScalarRoot318.norm_ne _ hn0 hn1)
  have hP : normProduct labels≠0 := normProduct_ne labels (fun j => odd_nonzero _ (hn j))
  have hs : (3:ℚ)^N≠0 := pow_ne_zero _ (by norm_num)
  have h20 : padicValRat 2 (3:ℚ)=0 := by
    simpa using AnchorNorm318.rational_unit_value 2 3 1 (by norm_num) (by norm_num)
  have h30 : padicValRat 3 (4096:ℚ)=0 := by
    simpa using AnchorNorm318.rational_unit_value 3 4096 1 (by norm_num) (by norm_num)
  have h212 : padicValRat 2 (4096:ℚ)=12 := by
    rw [show (4096:ℚ)=2^12 by norm_num,padicValRat.pow,padicValRat.self (by norm_num)]
    norm_num
  obtain ⟨p2,p3⟩ := actual_product_depths labels hn
  have hfirst2 : padicValRat 2 (4096*normProduct labels)=0 := by
    rw [padicValRat.mul (by norm_num) hP,h212,p2]
    norm_num
  have hfirst3 : padicValRat 3 (4096*normProduct labels)=0 := by
    rw [padicValRat.mul (by norm_num) hP,h30,p3]
    norm_num
  have hsecond2 : 0<padicValRat 2
      (ActualScalarRoot318.inverseNorm (labels 1)/(3:ℚ)^N) := by
    rw [padicValRat.div hI hs,scalar_norm_two _ hn0 hn1,padicValRat.pow,h20]
    norm_num
    omega
  obtain ⟨hr,hv2⟩ := ScalarPackedLocalUnit318.unit_add_small 2
    (4096*normProduct labels) (ActualScalarRoot318.inverseNorm (labels 1)/(3:ℚ)^N)
    (mul_ne_zero (by norm_num) hP) hfirst2 hsecond2
  have heven : Even (labels 1-1) := by
    obtain ⟨k,hk⟩ := hn 1
    exact ⟨k,by omega⟩
  have hsecond3 : 0≤padicValRat 3
      (ActualScalarRoot318.inverseNorm (labels 1)/(3:ℚ)^N) := by
    rw [padicValRat.div hI hs,scalar_norm_three _ hn0 hn1 heven,
      padicValRat.pow,padicValRat.self (by norm_num)]
    norm_num
    omega
  have hsum := padicValRat.min_le_padicValRat_add (p:=3) hr
  rw [hfirst3,min_eq_left hsecond3] at hsum
  exact ⟨hr,hv2,hsum⟩

end ActualAnchorRatio318
