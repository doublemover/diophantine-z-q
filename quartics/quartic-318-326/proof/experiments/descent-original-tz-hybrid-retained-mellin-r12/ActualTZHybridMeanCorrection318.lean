module
public import ActualTZHybridMeanAverage318
public import ActualTZActualCollisionAverage318
public import ActualTZOrdinaryMomentUniformIndex318
import all ActualTZPhysicalCorrectionBound318
import all ActualTZCollisionPrimePartition318
import all ActualTZMultiLinearCRT318
import all ActualTZHybridCanonicalWrap318
public section
noncomputable section
namespace ActualTZHybridMeanCorrection318
open scoped BigOperators
open ActualTZHybridCanonicalWrap318
open ActualTZHybridCanonicalWrap318.Context (Pair)
open ActualTZHybridGrid318 (dim)
open ActualTZHybridMeanAverage318 ActualTZHybridMeanCell318 ActualTZLiteralLowIntegral318
open ActualTZPhysicalEulerSplit318 ActualTZPhysicalCorrectionBound318
open ActualTZCollisionPrimePartition318 ActualTZWeightedPrimePrefix318
open ActualTZLiteralMellinTensor318 ActualTZLowFrequencyPole318
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {a t s : ℕ} (X : Context a t s I)

@[expose] def density : ℝ :=
  (Fintype.card X.Keys:ℝ)*(Fintype.card (Pair I):ℝ)*((2:ℝ)^(dim a t s)*
    (dim a t s:ℝ)*2)

def budget (P : ℕ) : ℝ :=
  let G := goodConst (Fintype.card I)*(∑ q∈offWheel (primorial X.y) P,(1/(q:ℝ))^2)+badConst (Fintype.card I)*extra (primorial X.y) P X.keyPrime
  (Real.exp G-1)+Real.exp G*(∑ q∈regular X.y X.N X.keyPrime,
    prefixWeight (badConst (Fintype.card I)) q*(density X*(1/(q:ℝ)+1/(X.minLen:ℝ))))

theorem exact_hit (z : X.G) (w : X.Keys) (q : ℕ) :
    ActualTZPhysicalCorrectionBound318.hit (primorial X.y) q (X.wrapped z w) X.base ↔
      X.hit q z w := by
  unfold Context.hit
  constructor
  · rintro ⟨i,j,hij,hd⟩
    refine ⟨⟨(i,j),hij⟩,?_⟩
    rw [X.physical_value z w _ 0,zero_add,zero_add]
    simpa only [ActualTZMultiLinearCRT318.physicalConst,Context.base] using hd
  · rintro ⟨⟨⟨i,j⟩,hij⟩,hd⟩
    rw [X.physical_value z w _ 0,zero_add,zero_add] at hd
    exact ⟨i,j,hij,by simpa only [ActualTZMultiLinearCRT318.physicalConst,Context.base] using hd⟩

theorem angular (P : ℕ) (T : ℝ) (hT : 0<T) (ξ : Slot I→ℝ) :
    (∑ zw : X.G×X.Keys,X.mass zw.1*X.θ zw.1 zw.2*
      ‖correctionAt (primorial X.y) P (X.wrapped zw.1 zw.2) X.base T ξ-1‖)≤budget X (P+1) := by
  simp only [Fintype.sum_prod_type,correctionAt]
  have H := ActualTZActualCollisionAverage318.corrected_average (primorial X.y) (P+1) X.y X.N X.keyPrime
    X.wrapped (fun _ _=>X.base) X.mass X.θ (1/T) (by positivity)
    (fun i=>shift T (ξ (i,true))) (fun i=>shift T (ξ (i,false)))
    (fun i=>le_of_eq (shift_re T (ξ (i,true))).symm)
    (fun i=>le_of_eq (shift_re T (ξ (i,false))).symm)
    (fun q hq hy=>hq.dvd_primorial_iff.2 hy)
    (fun z=>by unfold Context.mass; positivity) (fun z w=>(X.θ_bounds z w).1)
    X.retained_mass (fun _ _ _ i=>base_unit X i)
    (fun z w hw q _ hq=>by
      exact X.horizon_hit q z w hw ((exact_hit X z w q).1 hq))
    X.minLen (density X) (by exact_mod_cast (lt_min X.hJ X.hM))
  have H' := H (fun q hq=>by
    obtain ⟨hP,hy,hD⟩ := Finset.mem_filter.mp hq
    simpa only [exact_hit X] using X.sparse q (Nat.prime_of_mem_primesBelow hP) hy hD)
  simpa only [Finset.mul_sum,mul_assoc,budget] using H'

theorem budget_nonneg (P : ℕ) : 0≤budget X (P+1) := by
  refine le_trans (Finset.sum_nonneg ?_) (angular X P 1 zero_lt_one (fun _=>0))
  intro zw _
  exact mul_nonneg (mul_nonneg (by unfold Context.mass; positivity)
    (X.θ_bounds zw.1 zw.2).1) (norm_nonneg _)

end ActualTZHybridMeanCorrection318
