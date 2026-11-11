module
public import FinitePrimeSubpower318
public section
noncomputable section
namespace OriginalGlobalBadMass318
open scoped BigOperators
open LiteralSliceModulus318 OriginalBadSliceLogWeight318 OriginalBadSlicePointTail318
open FinitePrimeSubpower318
set_option maxHeartbeats 2500000

/-- All possible NONZERO labels of an original source point in the box.
Both signs are retained. Zero-label strata are deliberately separate. -/
@[expose] def labels (B : ℕ) : Finset ℤ := (Finset.Icc (-(2*B:ℤ)) (2*B:ℤ)).erase 0
lemma label_ne_zero (B : ℕ) (t : ℤ) (ht : t∈labels B) : t≠0 :=
  (Finset.mem_erase.mp ht).1
lemma label_bound (B : ℕ) (t : ℤ) (ht : t∈labels B) : t.natAbs≤2*B := by
  have hh := Finset.mem_Icc.mp (Finset.mem_erase.mp ht).2
  have ha : |t|≤(2*B:ℤ) := abs_le.mpr hh
  have hn : (t.natAbs:ℤ)≤(2*B:ℤ) := by simpa only [Int.natCast_natAbs] using ha
  exact_mod_cast hn

lemma labels_card (B : ℕ) : (labels B).card=4*B := by
  have hz : (0:ℤ)∈Finset.Icc (-(2*B:ℤ)) (2*B:ℤ) := Finset.mem_Icc.mpr (by constructor <;> omega)
  rw [labels,Finset.card_erase_of_mem hz,Int.card_Icc]
  omega

variable {J : Type*} [Fintype J] [DecidableEq J]
/-- The actual original weighted mass, summed over every nonzero label
in one of the two original charts, not over chosen residues or samples. -/
@[expose] def totalMass (B : ℕ) (κ : ℤ) (side : Bool) (T : ℝ) (γ : J → ℤ) : ℝ :=
  ∑ t∈labels B, logarithmicMass B κ t side T γ

lemma fixed_label_uniform (B : ℕ) (hB : 1≤B) (κ t : ℤ) (ht : t∈labels B)
    (side : Bool) (T : ℝ) (hT : 0<T) (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    logarithmicMass B κ t side T γ*T^3≤
      93312*supportConstant 4 δ*((2*B:ℝ)^δ)*(B:ℝ)^4*weightCeiling B γ := by
  have hne := label_ne_zero B t ht
  have htb := label_bound B t ht
  have hM : (modulus κ t:ℝ)≤2*(B:ℝ) := by
    exact_mod_cast (modulus_le_label κ t hne).trans htb
  have hω : (4:ℝ)^(retained κ t).card≤supportConstant 4 δ*((2*B:ℝ)^δ) :=
    (actual_retained_bound κ t δ hδ).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hM hδ.le)
        (constant_pos 4 δ (by norm_num)).le)
  have hW := weightCeiling_nonneg B hB γ
  have hC := (constant_pos 4 δ (by norm_num)).le
  have hR : 0≤(2*(B:ℝ))^δ := Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ (46656*(4:ℝ)^(retained κ t).card*(modulus κ t:ℝ)*(B:ℝ)^3)*weightCeiling B γ :=
      actual_weighted_bad_slice_tail B hB κ t hne htb side T hT γ
    _ ≤ (46656*(supportConstant 4 δ*((2*B:ℝ)^δ))*(2*(B:ℝ))*(B:ℝ)^3)*weightCeiling B γ := by
      gcongr
    _ = _ := by ring

/-- The complete bad-lattice contribution in one original chart.
No Rankin multiplicity input is needed here: q(t)≤2B and all4B actual
nonzero signed labels are summed directly. The only subpower estimate
is constructed from their literal distinct prime supports. -/
theorem all_label_weighted_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (side : Bool)
    (T : ℝ) (hT : 0<T) (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    totalMass B κ side T γ*T^3≤
      373248*supportConstant 4 δ*((2*B:ℝ)^δ)*(B:ℝ)^5*weightCeiling B γ := by
  classical
  rw [totalMass,Finset.sum_mul]
  calc
    _ ≤ ∑ _t∈labels B, 93312*supportConstant 4 δ*((2*B:ℝ)^δ)*(B:ℝ)^4*weightCeiling B γ :=
      Finset.sum_le_sum (fun t ht => fixed_label_uniform B hB κ t ht side T hT γ δ hδ)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,labels_card]; push_cast; ring

/-- Standard power formulation with a constructed supportConstant depending
only onδ. κ and the actual labels are not hidden in this supportConstant. -/
@[expose] def tailConstant (δ : ℝ) : ℝ := 373248*supportConstant 4 δ*(2:ℝ)^δ
lemma tailConstant_pos (δ : ℝ) : 0<tailConstant δ := by
  have h := constant_pos 4 δ (by norm_num)
  dsimp [tailConstant]
  positivity

theorem power_weighted_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (side : Bool)
    (T : ℝ) (hT : 0<T) (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    totalMass B κ side T γ*T^3≤
      tailConstant δ*(B:ℝ)^((5:ℝ)+δ)*weightCeiling B γ := by
  have hpos : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  have h := all_label_weighted_tail B hB κ side T hT γ δ hδ
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hpos.le] at h
  rw [Real.rpow_add hpos,Real.rpow_natCast]
  dsimp [tailConstant]
  convert h using 1 <;> ring

end OriginalGlobalBadMass318
