module
public import ActualTZPhysicalUnitMass318
public import ActualTZPhysicalWrapCorrection318
public import ActualTZLiteralLowIntegral318
import all ActualTZSharedXDivisorAverage318
import all ActualTZPhysicalWrapCorrection318
public section
noncomputable section
namespace ActualTZLiteralOrdinaryCorrection318
open scoped BigOperators
open ActualTZLiteralPhysicalWrapCarrier318 ActualTZSharedXDivisorAverage318 ActualTZPhysicalUnitMass318
open ActualTZPhysicalWrapCorrection318 ActualTZPhysicalEulerSplit318 ActualTZPhysicalCorrectionBound318
open ActualTZCollisionPrimePartition318 ActualTZWeightedPrimePrefix318
open ActualTZLiteralLowIntegral318 ActualTZLowFrequencyPole318
open ActualTZRelabelPhysicalGrid318 ActualTZLiteralMellinTensor318

variable {m a b j : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
variable {S : ActualTZJointPolynomialForms318.Terminal m a b} (X : Context S I)

/-- Explicit uniform analytic correction FOR THE EXISTING
actual carrier. P is the finite Euler universe, and X.N is the
different physical argument horizon. No comparison P≤2X.N. -/
def correctionBudget (P K : ℕ) : ℝ :=
  let G := goodConst (Fintype.card I)*(∑ p∈offWheel (primorial X.y) P,(1/(p:ℝ))^2)+
    badConst (Fintype.card I)*extra (primorial X.y) P K
  let A := (Fintype.card X.Keys:ℝ)*(Fintype.card (Context.Pair I):ℝ)*
    ((2:ℝ)^(D m a j)*(D m a j:ℝ)*(2:ℝ))
  (Real.exp G-1)+Real.exp G*(∑ p∈regular X.y X.N K,
    prefixWeight (badConst (Fintype.card I)) p*(A*(1/(p:ℝ)+1/(X.M:ℝ))))

theorem exact_angular (N K : ℕ)
    (hK : ∀ p,¬p∣K→∀ r q,ActualTZIntegerGridMarker318.reduced (p:=p) (X.pairPol r q)≠0)
    (L : ℝ) (hL : 0<L) (ξ : Slot I→ℝ) :
    (∑ zr : X.OldGrid×X.Keys,mass X zr.1*X.theta zr.1 zr.2*
      ‖correctionAt (primorial X.y) N (X.wrapped zr.1 zr.2) X.base L ξ-1‖)≤
      correctionBudget X (N+1) K := by
  rw [flatten X]
  have H := correction_average X (N+1) K hK (1/L) (by positivity)
    (fun i=>shift L (ξ (i,true))) (fun i=>shift L (ξ (i,false)))
    (fun i=>le_of_eq (shift_re L (ξ (i,true))).symm)
    (fun i=>le_of_eq (shift_re L (ξ (i,false))).symm)
  exact H

theorem budget_nonneg (N K : ℕ)
    (hK : ∀ p,¬p∣K→∀ r q,ActualTZIntegerGridMarker318.reduced (p:=p) (X.pairPol r q)≠0) :
    0≤correctionBudget X (N+1) K := by
  refine le_trans (Finset.sum_nonneg ?_) (exact_angular X N K hK 1 zero_lt_one (fun _=>0))
  intro zr _
  exact mul_nonneg
    (mul_nonneg (by unfold mass; positivity) (X.theta_bounds zr.1 zr.2).1) (norm_nonneg _)

end ActualTZLiteralOrdinaryCorrection318
