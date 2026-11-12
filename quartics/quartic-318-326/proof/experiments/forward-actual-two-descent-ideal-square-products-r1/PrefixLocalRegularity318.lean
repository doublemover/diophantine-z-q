module
public import ArithmeticIndexRegularity318
public section
noncomputable section
namespace PrefixLocalRegularity318
open ArithmeticIndexRegularity318
open ConcreteG8Domain (K)
open CoherentMultipleCharts318 (chartU chartV)
open CoherentMultiplePrefix318 (u v)
open CompressedOrientation318 (k m D)
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

variable (p : ℕ) [Fact p.Prime]
  (hb : ∀ a b h₀ : ℤ, LocalIndexRegularity318.Regular h₀
      (fun h => ActualOrbitLocalFilter318.error p (a+b*h)))

include hb in
lemma commonU (h₀ : ℤ) : KRegular p h₀ chartU := by
  simpa only [zero_add,one_mul] using ArithmeticIndexRegularity318.chartU p hb 0 1 h₀
include hb in
lemma commonV (h₀ : ℤ) : KRegular p h₀ chartV := by
  simpa only [zero_add,one_mul] using ArithmeticIndexRegularity318.chartV p hb 0 1 h₀

include hb in
lemma actualU (labels : Fin 4 → ℤ) (h₀ : ℤ) (j : Fin 8) :
    KRegular p h₀ (fun h => u labels h j) := by
  fin_cases j
  all_goals first
    | simpa only [u,CoherentMultiplePrefix318.parameters,Fin.append_left,zero_add] using
        ArithmeticIndexRegularity318.chartU p hb 0 (labels _) h₀
    | simpa only [u,CoherentMultiplePrefix318.parameters,Fin.append_right,mul_sub,mul_one,
        sub_eq_add_neg,add_comm] using ArithmeticIndexRegularity318.chartU p hb (-labels _) (labels _) h₀

include hb in
lemma actualV (labels : Fin 4 → ℤ) (h₀ : ℤ) (j : Fin 8) :
    KRegular p h₀ (fun h => v labels h j) := by
  fin_cases j
  all_goals first
    | simpa only [v,CoherentMultiplePrefix318.parameters,Fin.append_left,zero_add] using
        ArithmeticIndexRegularity318.chartV p hb 0 (labels _) h₀
    | simpa only [v,CoherentMultiplePrefix318.parameters,Fin.append_right,mul_sub,mul_one,
        sub_eq_add_neg,add_comm] using ArithmeticIndexRegularity318.chartV p hb (-labels _) (labels _) h₀

include hb in
lemma shift (h₀ : ℤ) (hh : h₀≠0) : KRegular p h₀
    (fun h => CompressedAnchorWitness318.shiftWitness (chartU h) (chartV h)) := by
  have hu := commonU p hb h₀
  have hv := commonV p hb h₀
  have hu0 : chartU h₀≠0 := fun he => hh ((CoherentMultipleCharts318.chartU_zero_iff _).mp he)
  unfold CompressedAnchorWitness318.shiftWitness
  apply KRegular.div
  · exact KRegular.sub (KRegular.div (KRegular.mul (KRegular.const p h₀ k) hv) hu hu0)
      (KRegular.const p h₀ m)
  · index_regularity
  · exact CompressedAnchorWitness318.denominator_nonzero _

lemma reciprocal_fill (h₀ : ℤ) (w : ℤ → CircuitReplay.Assignment)
    (uu vv : ℤ → Fin 8 → K) (hw : ∀ i, QRegular p h₀ (fun h => w h i))
    (hu : ∀ j, KRegular p h₀ (fun h => uu h j)) (hv : ∀ j, KRegular p h₀ (fun h => vv h j))
    (i : ℕ) : QRegular p h₀ (fun h => ReciprocalChartWitness318.fill (w h) (uu h) (vv h) i) := by
  unfold ReciprocalChartWitness318.fill
  split
  all_goals try index_regularity
  · exact QRegular.div ((hu 2).pow 2).re (QRegular.const p h₀ 2) (by norm_num)

include hb in
lemma compressed_fill (h₀ : ℤ) (hh : h₀≠0) (w : ℤ → CircuitReplay.Assignment)
    (hw : ∀ i, QRegular p h₀ (fun h => w h i)) (i : ℕ) :
    QRegular p h₀ (fun h => CompressedAnchorWitness318.fill (w h) (chartU h) (chartV h) i) := by
  have hu := commonU p hb h₀
  have hs := shift p hb h₀ hh
  unfold CompressedAnchorWitness318.fill
  split_ifs <;> index_regularity

lemma guard_fill (h₀ : ℤ) (w : ℤ → CircuitReplay.Assignment)
    (uu vv : ℤ → Fin 8 → K) (hw : ∀ i, QRegular p h₀ (fun h => w h i))
    (hu : ∀ j, KRegular p h₀ (fun h => uu h j)) (hv : ∀ j, KRegular p h₀ (fun h => vv h j))
    (hg : RealGuardWitness318.Guards (uu h₀)) (i : ℕ) :
    QRegular p h₀ (fun h => RealGuardWitness318.fill (w h) (uu h) (vv h) i) := by
  have hd (j : Fin 4) : KRegular p h₀ (fun h => RealGuardWitness318.denominator (uu h) j) := by
    unfold RealGuardWitness318.denominator
    index_regularity
  have hr (j : Fin 4) : KRegular p h₀ (fun h => RealGuardWitness318.root (uu h) (vv h) j) := by
    unfold RealGuardWitness318.root
    apply KRegular.div
    · unfold RealGuardWitness318.numerator
      index_regularity
    · exact hd j
    · exact RealGuardWitness318.denominator_ne _ _ (hg j)
  have hg' (j : Fin 4) : QRegular p h₀ (fun h => (RealGuardWitness318.denominator (uu h) j).re⁻¹) :=
    QRegular.inv (hd j).re (hg j)
  unfold RealGuardWitness318.fill
  split <;> index_regularity

include hb in
/-- Every coordinate of the literal prefix assignment is locally regular
on its actual domain. Guards are required only at the center, not at later h. -/
theorem prefix (q : ℚ) (labels : Fin 4 → ℤ) (h₀ : ℤ) (hh : h₀≠0)
    (hg : RealGuardWitness318.Guards (u labels h₀)) (i : ℕ) :
    QRegular p h₀ (fun h => CoherentMultiplePrefix318.witness q labels h i) := by
  apply guard_fill p h₀ _ _ _ _ (actualU p hb labels h₀) (actualV p hb labels h₀) hg i
  intro j
  apply compressed_fill p hb h₀ hh
  intro k
  exact reciprocal_fill p h₀ (fun _ _ => q) _ _ (fun _ => QRegular.const p h₀ q)
    (actualU p hb labels h₀) (actualV p hb labels h₀) k

end PrefixLocalRegularity318
