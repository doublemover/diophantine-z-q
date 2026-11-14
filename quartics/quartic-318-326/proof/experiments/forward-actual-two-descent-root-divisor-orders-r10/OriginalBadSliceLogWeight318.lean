module
public import OriginalBadSlicePointTail318
public section
noncomputable section
namespace OriginalBadSliceLogWeight318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralSliceBoxCount318 LiteralSliceModulus318 IntegerResidueBoxCount318
open OriginalBadSlicePointTail318 OriginalWeightedSelberg318
set_option maxHeartbeats 3500000

@[expose] def FiveBox (B : ℕ) := (Interval B×Interval B)×(Interval B×Interval B)×Interval B
@[expose] def boxed (B : ℕ) (κ label : ℤ) (side : Bool) : BoundedSlice B κ label side → FiveBox B := by
  intro v
  obtain ⟨ha,hb,hc,hd,hw⟩ := v.2
  exact ((⟨v.1.1.1.1.1,Finset.mem_Icc.mpr ha⟩,⟨v.1.1.1.1.2,Finset.mem_Icc.mpr hb⟩),
    (⟨v.1.1.1.2.1.1,Finset.mem_Icc.mpr hc⟩,⟨v.1.1.1.2.1.2,Finset.mem_Icc.mpr hd⟩),
    ⟨v.1.1.1.2.2,Finset.mem_Icc.mpr hw⟩)

lemma boxed_injective (B : ℕ) (κ label : ℤ) (side : Bool) : Function.Injective (boxed B κ label side) := by
  intro v w he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : FiveBox B => ((z.1.1.1,z.1.2.1),(z.2.1.1.1,z.2.1.2.1),z.2.2.1)) he

instance boundedSlice_finite (B : ℕ) (κ label : ℤ) (side : Bool) : Finite (BoundedSlice B κ label side) :=
  Finite.of_injective (boxed B κ label side) (boxed_injective B κ label side)

lemma square_bound (B : ℕ) (a : ℤ) (ha : -(B:ℤ)≤a ∧ a≤B) : a^2≤(B:ℤ)^2 := by
  have hh := mul_nonneg (sub_nonneg.mpr ha.2) (show 0≤(B:ℤ)+a by omega)
  nlinarith

lemma form_abs_bound (B : ℕ) (g a b w : ℤ)
    (ha : -(B:ℤ)≤a ∧ a≤B) (hb : -(B:ℤ)≤b ∧ b≤B) (hw : -(B:ℤ)≤w ∧ w≤B) :
    |a^2+b^2+g*w^2|≤(2+|g|)*(B:ℤ)^2 := by
  have hA := square_bound B a ha
  have hB := square_bound B b hb
  have hW := mul_le_mul_of_nonneg_left (square_bound B w hw) (abs_nonneg g)
  calc
    _ ≤ |a^2+b^2|+|g*w^2| := abs_add _ _
    _ = a^2+b^2+|g|*w^2 := by
      rw [abs_of_nonneg (by positivity),abs_mul,abs_of_nonneg (sq_nonneg w)]
    _ ≤ (2+|g|)*(B:ℤ)^2 := by nlinarith

@[expose] def ceilingTerm (B : ℕ) (g : ℤ) : ℝ := (2+|(g:ℝ)|)*(B:ℝ)^2
lemma ceilingTerm_one_le (B : ℕ) (hB : 1≤B) (g : ℤ) : 1≤ceilingTerm B g := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hb 2
  have hh := mul_nonneg (abs_nonneg (g:ℝ)) (sq_nonneg (B:ℝ))
  dsimp [ceilingTerm]
  nlinarith

variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def weightCeiling (B : ℕ) (γ : J → ℤ) : ℝ := ∏ j, Real.log (ceilingTerm B (γ j))
lemma weightCeiling_nonneg (B : ℕ) (hB : 1≤B) (γ : J → ℤ) : 0≤weightCeiling B γ := by
  exact Finset.prod_nonneg (fun j hj => Real.log_nonneg (ceilingTerm_one_le B hB (γ j)))

/-- Bound the ACTUAL original product of logarithms, not a newly supplied
weight. Original a,b,w are bounded in the five-coordinate source box. -/
theorem original_weight_bound (B : ℕ) (hB : 1≤B) (κ label : ℤ) (side : Bool)
    (γ : J → ℤ) (v : BoundedSlice B κ label side) :
    weight κ γ v.1.1≤weightCeiling B γ := by
  classical
  obtain ⟨ha,hb,hc,hd,hw⟩ := v.2
  apply Finset.prod_le_prod
  · intro j hj
    exact Real.log_nonneg (le_max_left _ _)
  · intro j hj
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    apply max_le
    · exact ceilingTerm_one_le B hB (γ j)
    · have hz := form_abs_bound B (γ j) v.1.1.1.1.1 v.1.1.1.1.2 v.1.1.1.2.2 ha hb hw
      have hn : ((form κ γ j v.1.1).natAbs:ℤ)≤(2+|γ j|)*(B:ℤ)^2 := by
        rw [Int.natCast_natAbs]
        exact hz
      dsimp [ceilingTerm]
      exact_mod_cast hn

/-- Exact logarithmic mass of all ACTUAL original bad slice points. -/
@[expose] def logarithmicMass (B : ℕ) (κ label : ℤ) (side : Bool) (T : ℝ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (BadSlice B κ label side T) := Fintype.ofFinite _
  exact ∑ v : BadSlice B κ label side T, weight κ γ v.1.1.1

lemma mass_le_card (B : ℕ) (hB : 1≤B) (κ label : ℤ) (side : Bool) (T : ℝ) (γ : J → ℤ) :
    logarithmicMass B κ label side T γ≤(Nat.card (BadSlice B κ label side T):ℝ)*weightCeiling B γ := by
  classical
  letI : Fintype (BadSlice B κ label side T) := Fintype.ofFinite _
  calc
    _ ≤ ∑ _v : BadSlice B κ label side T, weightCeiling B γ :=
      Finset.sum_le_sum (fun v hv => original_weight_bound B hB κ label side γ v.1)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]

/-- Fixed-label weighted ORIGINAL bad-lattice contribution, with actual
logarithmic weights and no supplied point-mass or weight-bound input. -/
theorem actual_weighted_bad_slice_tail (B : ℕ) (hB : 1≤B) (κ label : ℤ) (hlabel : label≠0)
    (hlabelB : label.natAbs≤2*B) (side : Bool) (T : ℝ) (hT : 0<T) (γ : J → ℤ) :
    logarithmicMass B κ label side T γ*T^3≤
      (46656*(4:ℝ)^(retained κ label).card*(modulus κ label:ℝ)*(B:ℝ)^3)*weightCeiling B γ := by
  have hcount := actual_bad_slice_tail B κ label hlabel hlabelB side T hT
  calc
    _ ≤ ((Nat.card (BadSlice B κ label side T):ℝ)*weightCeiling B γ)*T^3 :=
      mul_le_mul_of_nonneg_right (mass_le_card B hB κ label side T γ) (pow_nonneg hT.le 3)
    _ = ((Nat.card (BadSlice B κ label side T):ℝ)*T^3)*weightCeiling B γ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (weightCeiling_nonneg B hB γ)

end OriginalBadSliceLogWeight318
