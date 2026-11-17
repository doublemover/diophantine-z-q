module
public import OriginalUniformEulerRankin318
public import OriginalGlobalBadMass318
public section
noncomputable section
namespace OriginalSignedLabelRankin318
open scoped BigOperators
open OriginalGlobalBadMass318 OriginalUniformGoodFamily318
open OriginalRetainedFamilyWeight318 OriginalUniformEulerRankin318
set_option maxHeartbeats 7500000

/-- Same ORIGINAL signed nonzero slice labels as the weighted bad-tail
consumer. A label is injected into its sign and actual positive magnitude;
there is no change to label choice order or omission of negative slices. -/
@[expose] def signMagnitude (B : ℕ) (t : ↥(labels B)) : Bool×↥(Finset.Icc 1 (2*B)) :=
  (decide (t.1<0),⟨t.1.natAbs,Finset.mem_Icc.mpr ⟨by
    have hh := Int.natAbs_pos.mpr (label_ne_zero B t.1 t.2)
    omega,label_bound B t.1 t.2⟩⟩)

lemma signMagnitude_injective (B : ℕ) : Function.Injective (signMagnitude B) := by
  intro a b he
  have hs : decide (a.1<0)=decide (b.1<0) := congrArg Prod.fst he
  have hn : a.1.natAbs=b.1.natAbs := congrArg (fun z : Bool×↥(Finset.Icc 1 (2*B)) => z.2.1) he
  have ha : |a.1|=|b.1| := by
    simpa only [Int.natCast_natAbs] using congrArg (fun n : ℕ => (n:ℤ)) hn
  apply Subtype.ext
  by_cases hneg : a.1<0
  · have hb : b.1<0 := by by_contra hh;simp [hneg,hh] at hs
    exact neg_injective (by simpa only [abs_of_neg hneg,abs_of_neg hb] using ha)
  · have hb : ¬b.1<0 := by intro hh;simp [hneg,hh] at hs
    simpa only [abs_of_nonneg (le_of_not_gt hneg),abs_of_nonneg (le_of_not_gt hb)] using ha

lemma actual_signed_to_positive (κ : ℤ) (B : ℕ) :
    (∑ t∈labels B,familyWeight κ t)≤2*(∑ n∈Finset.Icc 1 (2*B),familyWeight κ (n:ℤ)) := by
  classical
  have hh := hasSum_le_inj (signMagnitude B) (signMagnitude_injective B)
    (fun n _ => weight_nonneg κ n.2.1)
    (fun t => le_of_eq (signed_weight κ t.1 (label_ne_zero B t.1 t.2)).symm)
    (hasSum_fintype (fun t : ↥(labels B) => familyWeight κ t.1))
    (hasSum_fintype (fun n : Bool×↥(Finset.Icc 1 (2*B)) => weight κ n.2.1))
  have hw : (∑ n∈Finset.Icc 1 (2*B),weight κ n)=∑ n∈Finset.Icc 1 (2*B),familyWeight κ (n:ℤ) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact actual_weight κ n (by have hh := Finset.mem_Icc.mp hn;omega)
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,Finset.sum_coe_sort] at hh
  rw [hw] at hh
  linarith only [hh]

/-- Genuine original signed-label Rankin bound. ALL powers of excluded
primes dividing2*kappa are contained in the explicit finite local-series
factor of rankinConstant; the constant is independent of source boxB. -/
theorem actual_original_label_sum (κ : ℤ) (hκ : κ≠0) (δ : ℝ) (hδ : 0<δ) (B : ℕ) :
    (∑ t∈labels B,familyWeight κ t)≤2*rankinConstant κ δ*(2*(B:ℝ))^δ := by
  have hh := actual_signed_to_positive κ B
  have hp := mul_le_mul_of_nonneg_left (actual_positive_label_sum κ hκ δ hδ (2*B))
    (by norm_num : (0:ℝ)≤2)
  push_cast at hp
  nlinarith only [hh,hp]

end OriginalSignedLabelRankin318
