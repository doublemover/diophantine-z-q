module
public import ActualTZLiteralReferenceNear318
public import ActualTZLiteralHighIntegrand318
public import ActualTZAngularKernelMain318
public import ActualTZPhysicalEulerSplit318
import all ActualTZLiteralHighIntegrand318
public section
noncomputable section
namespace ActualTZLiteralLowIntegral318
open MeasureTheory
open scoped BigOperators
open ActualTZLiteralReferenceNear318 ActualTZThreeNearFactors318
open ActualTZLowFrequencyPole318 ActualTZLiteralHighIntegrand318
open ActualTZPhysicalEulerSplit318 ActualTZWheelZero318 ActualTZWheelLowBand318
open ActualTZLiteralMellinTensor318 ActualTZMellinFiniteGuard318 ActualTZLiteralSchwartz318
open ActualTZAngularKernelMain318 ActualTZAngularTensorTail318

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

@[expose] def direct (ξ : Slot I→ℝ) (b : Bool) : I→ℝ := fun i=>ξ (i,b)

@[expose] def correctionAt (W N : ℕ) (a : I→ℤ) (b : I→ℕ)
    (L : ℝ) (ξ : Slot I→ℝ) : ℂ :=
  corrected W (N+1) a b (fun i=>shift L (ξ (i,true))) (fun i=>shift L (ξ (i,false)))

theorem factored (C : Cutoff) (W N : ℕ) (hW : 0<W)
    (hP : W.primeFactors⊆Nat.primesBelow (N+1))
    (a : I→ℤ) (b : I→ℕ) (hU : ∀ i,W.Coprime (b i)) (L : ℝ) (hL : 0<L) (ξ : Slot I→ℝ) :
    integrand C W (N+1) a b L ξ =
      (∏ j : Slot I,φ C (ξ j))*
        (sharedReference W N L (direct ξ true) (direct ξ false)*correctionAt W N a b L ξ) := by
  have hσ : (0:ℝ)<1/L := by positivity
  have hs (i : I) : 1/L≤(s1 L ξ i).re := le_of_eq ((real_parts L ξ i).1.symm)
  have ht (i : I) : 1/L≤(s2 L ξ i).re := le_of_eq ((real_parts L ξ i).2.symm)
  have H := normalized_split W (N+1) hW hP a b hU (1/L) hσ (s1 L ξ) (s2 L ξ) hs ht L
  rw [integrand,signed_is_actual]
  calc
    _ = (∏ j : Slot I,φ C (ξ j))*
        (normalizer (I:=I) W L*actualPartial W (N+1) a b (s1 L ξ) (s2 L ξ)) := by ring
    _ = _ := by
      unfold normalizer
      change (∏ j : Slot I,φ C (ξ j))*
        ((alpha W*(L:ℂ))^Fintype.card I*actualPartial W (N+1) a b (s1 L ξ) (s2 L ξ))=_
      rw [H]
      simp only [sharedReference,multiplier,direct,correctionAt,s1,s2,shift] <;> ring

def weightedDifference (C : Cutoff) (W N : ℕ)
    (a : J→I→ℤ) (b : J→I→ℕ) (w : J→ℝ) (L : ℝ) (ξ : Slot I→ℝ) : ℂ :=
  ∑ j : J,(w j:ℂ)*(integrand C W (N+1) (a j) (b j) L ξ-mainDensity C ξ)

private theorem point_bound (C : Cutoff) (W N : ℕ) (hW : 0<W)
    (hP : W.primeFactors⊆Nat.primesBelow (N+1))
    (a : J→I→ℤ) (b : J→I→ℕ) (hU : ∀ j i,W.Coprime (b j i))
    (w : J→ℝ) (hw : ∀ j,0≤w j) (hTotal : (∑ j : J,w j)≤1)
    (L : ℝ) (hL : 0<L) (ξ : Slot I→ℝ) (δ E : ℝ) (hδ : 0≤δ)
    (hRef : ‖sharedReference W N L (direct ξ true) (direct ξ false)-
          sharedKernel (direct ξ true) (direct ξ false)‖≤
        ‖sharedKernel (direct ξ true) (direct ξ false)‖*δ)
    (hC : (∑ j : J,w j*‖correctionAt W N (a j) (b j) L ξ-1‖)≤E) :
    ‖weightedDifference C W N a b w L ξ‖≤‖mainDensity C ξ‖*(δ+(1+δ)*E) := by
  let F := ∏ j : Slot I,φ C (ξ j)
  let K := sharedKernel (direct ξ true) (direct ξ false)
  let P := sharedReference W N L (direct ξ true) (direct ξ false)
  let c (j : J) := correctionAt W N (a j) (b j) L ξ
  have hMain : mainDensity C ξ=F*K := mainDensity_product C ξ
  have hEach (j : J) :
      integrand C W (N+1) (a j) (b j) L ξ-mainDensity C ξ=F*(P*c j-K) := by
    rw [factored C W N hW hP _ _ (hU j) L hL ξ,hMain]
    change F*(P*c j)-F*K=F*(P*c j-K)
    ring
  have H := average_cell_near w hw hTotal P K c δ E hδ hRef hC
  unfold weightedDifference
  calc
    _ ≤ ∑ j : J,‖(w j:ℂ)*(integrand C W (N+1) (a j) (b j) L ξ-mainDensity C ξ)‖ :=
      norm_sum_le _ _
    _ = ‖F‖*(∑ j : J,w j*‖P*c j-K‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hEach j,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw j)]
      ring
    _ ≤ _ := by
      rw [hMain,norm_mul,mul_assoc]
      exact mul_le_mul_of_nonneg_left H (norm_nonneg F)

/-- Native accepting integral on the SAME angular band and literal
signed Euler terms. Supply only the weighted absolute correction
bound from the true physical marginals, not pointwise regularity. -/
theorem weighted_low (C : Cutoff) (W N : ℕ) (hW : 0<W)
    (hP : W.primeFactors⊆Nat.primesBelow (N+1))
    (a : J→I→ℤ) (b : J→I→ℕ) (hU : ∀ j i,W.Coprime (b j i))
    (w : J→ℝ) (hw : ∀ j,0≤w j) (hTotal : (∑ j : J,w j)≤1)
    (L : ℝ) (hL : 0<L) (δ E : ℝ) (hδ : 0≤δ) (hE : 0≤E)
    (hRef : ∀ ξ∈fullBand I (band L),
      ‖sharedReference W N L (direct ξ true) (direct ξ false)-
        sharedKernel (direct ξ true) (direct ξ false)‖≤
          ‖sharedKernel (direct ξ true) (direct ξ false)‖*δ)
    (hC : ∀ ξ∈fullBand I (band L),
      (∑ j : J,w j*‖correctionAt W N (a j) (b j) L ξ-1‖)≤E) :
    ‖∫ ξ in fullBand I (band L),weightedDifference C W N a b w L ξ ∂μ I‖≤
      (δ+(1+δ)*E)*(∫ ξ,‖mainDensity C ξ‖ ∂μ I) := by
  let f := weightedDifference C W N a b w L
  let η := δ+(1+δ)*E
  have hη : 0≤η := by dsimp only [η]; positivity
  have hf : Integrable f (μ I) := by
    unfold f weightedDifference
    exact integrable_finsetSum _ (fun j _ =>
      ((literal_integrable C W (N+1) (a j) (b j) (hU j) L).sub (main_integrable C)).const_mul _)
  have hg : Integrable (fun ξ : Slot I→ℝ=>η*‖mainDensity C ξ‖) (μ I) :=
    (main_integrable C).norm.const_mul _
  calc
    _ ≤ ∫ ξ in fullBand I (band L),‖f ξ‖ ∂μ I := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ in fullBand I (band L),η*‖mainDensity C ξ‖ ∂μ I := by
      apply setIntegral_mono_on hf.norm.integrableOn hg.integrableOn (fullBand_measurable _)
      intro ξ hξ
      rw [mul_comm η]
      exact point_bound C W N hW hP a b hU w hw hTotal L hL ξ δ E hδ (hRef ξ hξ) (hC ξ hξ)
    _ ≤ ∫ ξ,η*‖mainDensity C ξ‖ ∂μ I :=
      setIntegral_le_integral hg (Filter.Eventually.of_forall (fun _=>mul_nonneg hη (norm_nonneg _)))
    _ = _ := by simp only [η,integral_const_mul]

end ActualTZLiteralLowIntegral318
