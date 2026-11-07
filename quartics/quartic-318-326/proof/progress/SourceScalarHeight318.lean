module
public import ScalarContactValuation318
public import SourceScalarDivisibility318
public import ConsumedContactHeight318
public import RationalSeparationBase
public section
noncomputable section
namespace SourceScalarHeight318
open CircuitReplay Raw318FinalReplay ScalarSource318 ScalarContactMap318
open ContactRadical318 ContactPrimeLimits318 ContactHeight318 NumberField
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Each actual good odd scalar contact contributes order8 to the same
coherently chosen scalar index. No local place or logarithm premise remains. -/
theorem labeled_prime_divisibility (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels:SourceLabelData318.Labels w source) (hb:beta w≠0) :
    ∀p∈contactPrimes (beta w).num (beta w).den,(p:ℤ)^8∣labels.c := by
  intro p hp
  have hprime:=member_prime (beta w).num (beta w).den p hp
  letI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨j,hj,hg,ho⟩ := (mem_contactPrimes _ _ p).mp hp
  obtain ⟨f,hf,hpos,hodd⟩ := ScalarContactValuation318.member_source_contact p _ w source hb hp
  exact SourceScalarDivisibility318.labeled_scalar_index p
    (good_ge_nineteen p hprime hg) w source labels f hf hpos hodd

/-- The complete source scalar height estimate. The only geometric input is
the explicitly named five-contact49/8 theorem. beta=0 is handled by height0,
not by applying the omitted-contact theorem at a forbidden point. -/
theorem labeled_scalar_height (hFive:FiveContact49Height) (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels:SourceLabelData318.Labels w source) :
    absLogHeight₁ (beta w)≤HeightSeparation318.heightConstant*|(labels.c:ℝ)|^((49:ℝ)/64) := by
  by_cases hb:beta w=0
  · rw [hb]
    convert ConsumedContactHeight318.rational_zero_height labels.c 8 using 1 <;> norm_num
  · exact ConsumedContactHeight318.scalar_order8 hFive (beta w)
      (source_forms_nonzero _ w source hb) labels.c
      (RawOddAnchorPoints318.scalar_label_nonzero w labels.c labels.scalar)
      (labeled_prime_divisibility w source labels hb)

lemma rational_height_eq_literal (q:ℚ) : absLogHeight₁ q=ZInQ.rationalLogHeight q := by
  rw [DetectorHeightTransfer318.rational_height_eq,Rat.logHeight₁_eq_log_max]
  simp only [ZInQ.rationalLogHeight,Nat.cast_max,Nat.cast_natAbs,Int.cast_abs]

/-- Exact scalar field consumed by final numerical separation: beta is the
literal 3723(2w0+1)^2, and the index size is the natural absolute value. -/
theorem labeled_scalar_comparison (hFive:FiveContact49Height) (w:Assignment)
    (source:Constraints (stage0 ((3:ℚ)^65536)) w)
    (labels:SourceLabelData318.Labels w source) :
    ZInQ.rationalLogHeight (3723*(2*w 0+1)^2)≤
      HeightSeparation318.heightConstant*(labels.c.natAbs:ℝ)^((49:ℝ)/64) := by
  have hh:=labeled_scalar_height hFive w source labels
  rw [rational_height_eq_literal] at hh
  simpa only [beta,Nat.cast_natAbs,Int.cast_abs] using hh

#print axioms labeled_prime_divisibility
#print axioms labeled_scalar_height
#print axioms rational_height_eq_literal
#print axioms labeled_scalar_comparison
end SourceScalarHeight318
