module
public import SelectedContactWeightValues318
public section
noncomputable section
namespace SelectedOppositeGood318
open CircuitReplay ConcreteG8Domain ConcretePadic318
open ContactPrimeForms318 ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ScaledContactWeights318 ScaledDetectorChain318 DetectorWeightPreparation318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- Only original fixed-prime avoidance remains here: actual selected primes
are large and avoid the fixed scales and the actual clearing denominator.
No delta-unit, weight parity or detector-leaf parity is assumed. -/
@[expose] def Avoidance (u w : ℤ) (hp : Values C u w) : Prop :=
  ∀ j : Fin 3, ∀ i : Fin 5,
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    76176<p ∧ rationalPlace p (ThreeDetectorArithmetic318.scales labels j)=0 ∧
      rationalPlace p (denominator C w)=0

/-- Complete opposite-weight/even-leaf hypotheses for the actual scaled
chain, with actual delta-unit production at every selected contact. -/
theorem actual_opposite (hn : ∀ j, labels j≠0) (q : ℚ) (h u w : ℤ)
    (hp : Values C u w) (ha : Avoidance C u w hp)
    (hzero : h≠0) (hone : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0)
    (j : Fin 3) (i : Fin 5) :
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    rationalPlace p (delta (ThreeDetectorArithmetic318.scales labels j) (ClearedContactForms318.parameter C u w))=0 ∧
    ∀ (rho : ℚ_[p]) (hr : rho^2=2),
      ∀ a∈ActualDetectorFold318.leaves
        (view (DetectorGateWitness318.witness q labels h)
          (ThreeDetectorArithmetic318.scales labels j) (ClearedContactForms318.parameter C u w)),
        ValuationEvenNormChain.OddAt (place p (-rho) (negative_root p rho hr)) a.1 ∧
        ValuationEvenNormChain.EvenAt (place p (-rho) (negative_root p rho hr)) a.2 := by
  dsimp only
  let p := (row C u w j i).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
  obtain ⟨hlarge,hcunit,hdunit⟩ := ha j i
  have hc : ThreeDetectorArithmetic318.scales labels j≠0 := by
    rw [scales_eq]
    exact scaleRoot_ne labels hn j
  have hd := denominator_ne C w hp.nonzero
  have hv := SelectedProductDepth318.factor_values (row C u w j)
    (row_pos C u w hp j) (row_prime C u w hp j) (row_distinct C hn u w hp j) i
  have ht : ClearedContactForms318.parameter C u w=(u:ℚ)/(denominator C w)^2 := rfl
  have hselected : rationalPlace p (DetectorPrimeProduct318.linear
      (ThreeDetectorArithmetic318.scales labels j) (u:ℚ) (denominator C w) i)=1 := by
    rw [linear_eq]
    simpa only [ite_true] using hv i
  have hdel := SelectedContactWeightValues318.selected_delta p hlarge _ _ _ hc hd hcunit hdunit i hselected
  have hweights := SelectedContactWeightValues318.weight_values p _ _ _ hc hd hcunit hdunit hdel
    (row C u w j) (linear_eq C u w j) (SelectedProductDepth318.actual_product C hn u w hp j i)
  rw [ht]
  refine ⟨hdel,?_⟩
  intro rho hr a hmem
  have h7 : ¬p∣49 := fun he => (by omega : ¬p≤49) (Nat.le_of_dvd (by norm_num) he)
  have heven := SelectedCurveUnits318.actual_even p (by omega) h7 rho hr q labels h
    hzero hone hg (ThreeDetectorArithmetic318.scales labels j)
    ((u:ℚ)/(denominator C w)^2) a hmem
  refine ⟨?_,heven⟩
  rw [leaves_weights] at hmem
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hmem
  exact SelectedContactWeightValues318.all_odd p (-rho) (negative_root p rho hr)
    _ _ hweights b.1

/-- The opposite dichotomy now follows for the actual whole chain without
any supplied leaf-parity family. -/
theorem actual_good (hn : ∀ j, labels j≠0) (q : ℚ) (h u w : ℤ)
    (hp : Values C u w) (ha : Avoidance C u w hp)
    (hzero : h≠0) (hone : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0)
    (j : Fin 3) (i : Fin 5) :
    let p := (row C u w j i).natAbs
    letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
    ∀ (rho : ℚ_[p]) (hr : rho^2=2),
      NormChainCompleteness.Good (place p (-rho) (negative_root p rho hr))
        (ActualDetectorFold318.chain (view (DetectorGateWitness318.witness q labels h)
          (ThreeDetectorArithmetic318.scales labels j) (ClearedContactForms318.parameter C u w))) := by
  dsimp only
  intro rho hr
  exact ActualDetectorFold318.good _ _
    ((actual_opposite C hn q h u w hp ha hzero hone hg j i).2 rho hr)

end SelectedOppositeGood318
