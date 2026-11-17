module
public import SeventeenScalarDepth318
public section
noncomputable section
namespace SeventeenScalarCenter318
open CoherentMultipleCharts318 (chartU)
open GeneratorScalarProgression318 (normCoefficient)
open ScalarPreparedResidues318 (residue modulus scalarLabel)
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Multiplication by85 is1 modulo6, preserves the original exact2/3
residue class, and enters the actual17 chart at index20 times an integer. -/
@[expose] def center (A B : ℕ) : ℕ := 85*residue A B
lemma center_positive (A B : ℕ) : 0<center A B := by
  unfold center
  exact Nat.mul_pos (by norm_num) (ScalarPreparedResidues318.residue_pos A B)
lemma center_congruence (A B : ℕ) : Nat.ModEq (modulus A B) (center A B) (residue A B) := by
  apply Nat.modEq_iff_dvd.mpr
  refine ⟨-14,?_⟩
  unfold center modulus
  push_cast
  ring
lemma center_index (A B : ℕ) (hA : 2≤A) :
    (center A B:ℤ)=20*((17:ℤ)*2^(A-2)*3^B) := by
  have ha : A=(A-2)+2 := by omega
  unfold center residue
  push_cast
  have hp : (2:ℤ)^A=2^(A-2)*4 := by
    calc
      (2:ℤ)^A = 2^((A-2)+2) := by rw [←ha]
      _ = 2^(A-2)*4 := by rw [pow_add]; norm_num
  rw [hp]
  ring
lemma center_depths (A B : ℕ) (hA : 2≤A) :
    0<padicValRat 17 (normCoefficient (chartU (center A B:ℤ))) ∧
    0<padicValRat 17 (2*((chartU (center A B:ℤ))^2).re) := by
  rw [center_index A B hA]
  have hd := SeventeenScalarDepth318.actual_depths 0
    ((17:ℤ)*2^(A-2)*3^B) (by positivity)
  simp only [pow_zero,mul_one,Nat.cast_zero,zero_add,mul_one] at hd
  have hn : (20:ℤ)*(17*2^(A-2)*3^B)≠0 := by positivity
  have hf := SeventeenScalarDepth318.half_trace_ne _ hn
  have htwo : padicValRat 17 (2:ℚ)=0 := by
    simpa using AnchorNorm318.rational_unit_value 17 2 1 (by norm_num) (by norm_num)
  rw [padicValRat.mul (by norm_num) hf,htwo,zero_add]
  constructor <;> omega

/-- The scalar label is now fixed after the actual common center, with
arbitrary remaining positive multiplier d. This retains the original Lucas
and physical-anchor construction while making its norm deeper than H. -/
theorem choose_label (A B N : ℕ) (hA : 2≤A) :
    ∃ e : ℕ, ∀ d : ℕ, d≠0 →
      let n := scalarLabel A B (PreparedAnchorLabels318.multiplier N (20*17^e*d))
      2*padicValRat 17 (normCoefficient (chartU (center A B:ℤ)))<
        2*padicValRat 17 (ActualScalarRoot318.inverseNorm n) := by
  let v := padicValRat 17 (normCoefficient (chartU (center A B:ℤ)))
  refine ⟨v.natAbs+1,?_⟩
  intro d hd
  have he := SeventeenScalarDepth318.label_depth A B N (v.natAbs+1) d hd
  have hv : v≤(v.natAbs:ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self v
  dsimp only at he ⊢
  push_cast at he
  change 2*v<_
  omega

/-- No additional valuation premise at17 remains for the scalar packed
unit at the constructed center and fixed labels. -/
theorem center_unit (a : ℤ) (A B N : ℕ) (hA : 2≤A) :
    ∃ e : ℕ, ∀ d : ℕ, ∀ hd : d≠0,
      let d' := PreparedAnchorLabels318.multiplier N (20*17^e*d)
      let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _
        (mul_ne_zero (by positivity) hd)
      let labels := FixedArithmeticLabels318.labels a A B d' hd'
      ScalarForwardWitness318.W
        (DetectorGateWitness318.witness (a:ℚ) labels (center A B:ℤ)) (labels 1)≠0 ∧
      padicValRat 17 (ScalarForwardWitness318.W
        (DetectorGateWitness318.witness (a:ℚ) labels (center A B:ℤ)) (labels 1))=0 := by
  obtain ⟨e,he⟩ := choose_label A B N hA
  refine ⟨e,?_⟩
  intro d hd
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier N (20*17^e*d)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _ (mul_ne_zero (by positivity) hd)
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  let w := DetectorGateWitness318.witness (a:ℚ) labels (center A B:ℤ)
  have hin : w 0=(a:ℚ) := DetectorGateWitness318.witness_input _ _ _
  have hh : (center A B:ℤ)≠0 := by exact_mod_cast ne_of_gt (center_positive A B)
  have hH : w 37≠0 := by rw [ScalarActualInputs318.detector37]; exact SeventeenScalarDepth318.norm_ne _ hh
  have hf : w 33≠0 := by rw [ScalarActualInputs318.detector33]; exact SeventeenScalarDepth318.half_trace_ne _ hh
  have hn := (ScalarPreparedResidues318.label_domains A B d' hd').1
  have hr : ScalarForwardWitness318.inputR (w 0)≠0 := by rw [hin]; have he := ScalarForwardWitness318.integer_inputR_large a; linarith
  have hrv : padicValRat 17 (ScalarForwardWitness318.inputR (w 0))=0 := by
    rw [hin]; exact (ScalarTwoThreePreparation318.input_values a).2.2
  apply (ScalarPackedLocalUnit318.actual_unit 17 w (labels 1) hr hf hH (by change scalarLabel A B d'≠0; omega)
    (by change scalarLabel A B d'≠1; omega) ?_ ?_ ?_)
  · rw [hrv,ScalarActualInputs318.detector37]
    exact (center_depths A B hA).1
  · rw [hrv,ScalarActualInputs318.detector33]
    exact (center_depths A B hA).2
  · rw [hrv,mul_zero,add_zero,ScalarActualInputs318.detector37]
    exact he d hd

end SeventeenScalarCenter318
