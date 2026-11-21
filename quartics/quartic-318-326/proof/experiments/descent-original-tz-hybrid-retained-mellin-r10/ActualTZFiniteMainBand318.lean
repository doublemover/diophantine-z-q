module
public import ActualTZPhysicalFiniteMain318
public import ActualTZLiteralLowIntegral318
public import ActualTZAngularKernelTail318
import all ActualTZLiteralHighIntegrand318
import all ActualTZLiteralLowIntegral318
public section
noncomputable section
namespace ActualTZFiniteMainBand318
open MeasureTheory
open scoped BigOperators
open ActualTZPhysicalFiniteMain318 ActualTZLiteralLowIntegral318
open ActualTZLiteralHighIntegrand318 ActualTZLiteralReferenceNear318
open ActualTZAngularKernelMain318 ActualTZAngularTensorTail318
open ActualTZLiteralMellinTensor318 ActualTZLiteralSchwartz318
open ActualTZLowFrequencyPole318 ActualTZLiteralAbsoluteEuler318
open ActualTZMultiSieveCell318

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

def exactMain (C : Cutoff) (W : ℕ) (a : I→ℤ) (b : I→ℕ) (R : ℝ) : ℝ :=
  finiteMain ((Nat.totient W:ℝ)/(W:ℝ)) R C.χ W a b

theorem integral_is_exactMain (C : Cutoff) (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (R : ℝ) (hR : 1<R) (hP : ⌊R⌋₊<P) :
    (∫ ξ,integrand C W P a b (Real.log R) ξ ∂μ I)=(exactMain C W a b R:ℂ) := by
  have H := finite_main_eq_integral C R hR W P a b hU hP
  unfold exactMain
  simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast] at H
  unfold integrand
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  exact H

private theorem diff_integrable (C : Cutoff) (W N : ℕ)
    (a : J→I→ℤ) (b : J→I→ℕ) (hU : ∀ j i,W.Coprime (b j i)) (w : J→ℝ) (L : ℝ) :
    Integrable (weightedDifference C W N a b w L) (μ I) := by
  unfold weightedDifference
  exact integrable_finsetSum _ (fun j _=>
    ((literal_integrable C W (N+1) (a j) (b j) (hU j) L).sub (main_integrable C)).const_mul _)

private theorem integrate_difference (C : Cutoff) (W N : ℕ)
    (a : J→I→ℤ) (b : J→I→ℕ) (hU : ∀ j i,W.Coprime (b j i)) (w : J→ℝ)
    (R : ℝ) (hR : 1<R) (hP : ⌊R⌋₊<N+1)
    (hχ : (∫ u in (0:ℝ)..1,|deriv C.χ u|^2)=1) :
    (∫ ξ,weightedDifference C W N a b w (Real.log R) ξ ∂μ I) =
      ((∑ j : J,w j*(exactMain C W (a j) (b j) R-1):ℝ):ℂ) := by
  unfold weightedDifference
  have H (j : J) :
      Integrable (fun ξ=>(w j:ℂ)*(integrand C W (N+1) (a j) (b j) (Real.log R) ξ-
          mainDensity C ξ)) (μ I) :=
    ((literal_integrable C W (N+1) (a j) (b j) (hU j) (Real.log R)).sub
       (main_integrable C)).const_mul _
  rw [integral_finsetSum _ (fun j _=>H j)]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,
    integral_sub (literal_integrable C W (N+1) (a j) (b j) (hU j) (Real.log R))
      (main_integrable C),
    integral_is_exactMain C W (N+1) _ _ (hU j) R hR hP,main_one C hχ]

private theorem high_weighted (C : Cutoff) (W N : ℕ) (hW : 0<W)
    (a : J→I→ℤ) (b : J→I→ℕ) (hU : ∀ j i,W.Coprime (b j i))
    (w : J→ℝ) (hw : ∀ j,0≤w j) (hTotal : (∑ j : J,w j)≤1) (L : ℝ) (hL : 1≤L) :
    let d := 4*(Fintype.card I+offCount I+2)
    ‖∫ ξ in (fullBand I (band L))ᶜ,weightedDifference C W N a b w L ξ ∂μ I‖ ≤
      ((2:ℝ)^(offCount I)/L^2)*(∫ ξ,moments C d ξ ∂μ I)+
      ∫ ξ in (fullBand I (band L))ᶜ,‖mainDensity C ξ‖ ∂μ I := by
  intro d
  let S := (fullBand I (band L))ᶜ
  let A := ((2:ℝ)^(offCount I)/L^2)*(∫ ξ,moments C d ξ ∂μ I)
  let B := ∫ ξ in S,‖mainDensity C ξ‖ ∂μ I
  have hA : 0≤A := mul_nonneg (by positivity) (integral_nonneg (moments_nonneg C d))
  have hB : 0≤B := integral_nonneg (fun _=>norm_nonneg _)
  unfold weightedDifference
  have hInt (j : J) :
      IntegrableOn (fun ξ=>(w j:ℂ)*(integrand C W (N+1) (a j) (b j) L ξ-
        mainDensity C ξ)) S (μ I) :=
    (((literal_integrable C W (N+1) (a j) (b j) (hU j) L).sub
      (main_integrable C)).const_mul _).integrableOn
  rw [integral_finsetSum _ (fun j _=>hInt j)]
  calc
    _ ≤ ∑ j : J,‖∫ ξ in S,(w j:ℂ)*(integrand C W (N+1) (a j) (b j) L ξ-
        mainDensity C ξ) ∂μ I‖ := norm_sum_le _ _
    _ ≤ ∑ j : J,w j*(A+B) := by
      apply Finset.sum_le_sum
      intro j _
      rw [integral_const_mul,integral_sub
        (literal_integrable C W (N+1) (a j) (b j) (hU j) L).integrableOn
        (main_integrable C).integrableOn,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (hw j)]
      apply mul_le_mul_of_nonneg_left _ (hw j)
      exact (norm_sub_le _ _).trans (add_le_add
        (high_error C W (N+1) hW _ _ (hU j) L hL)
        (norm_integral_le_integral_norm _))
    _ = (A+B)*(∑ j : J,w j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ A+B := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hTotal (add_nonneg hA hB)

/-- Full signed finite-main comparison on the actual weighted row.
The remaining arithmetic input is one weighted correction bound E
on the unchanged physical cells (not pointwise at each row); δ is
delivered by the fixed-wheel/reference low-frequency theorem. -/
theorem weighted_exact_main (C : Cutoff) (W N : ℕ) (hW : 0<W)
    (hWheel : W.primeFactors⊆Nat.primesBelow (N+1))
    (a : J→I→ℤ) (b : J→I→ℕ) (hU : ∀ j i,W.Coprime (b j i))
    (w : J→ℝ) (hw : ∀ j,0≤w j) (hTotal : (∑ j : J,w j)≤1)
    (R : ℝ) (hR : 1<R) (hP : ⌊R⌋₊<N+1) (hL : 1≤Real.log R)
    (hχ : (∫ u in (0:ℝ)..1,|deriv C.χ u|^2)=1)
    (δ E : ℝ) (hδ : 0≤δ) (hE : 0≤E)
    (hRef : ∀ ξ∈fullBand I (band (Real.log R)),
      ‖sharedReference W N (Real.log R) (direct ξ true) (direct ξ false)-
        sharedKernel (direct ξ true) (direct ξ false)‖≤
          ‖sharedKernel (direct ξ true) (direct ξ false)‖*δ)
    (hC : ∀ ξ∈fullBand I (band (Real.log R)),
      (∑ j : J,w j*‖correctionAt W N (a j) (b j) (Real.log R) ξ-1‖)≤E) :
    let L := Real.log R
    let d := 4*(Fintype.card I+offCount I+2)
    |∑ j : J,w j*(exactMain C W (a j) (b j) R-1)| ≤
      (δ+(1+δ)*E)*(∫ ξ,‖mainDensity C ξ‖ ∂μ I)+
      (((2:ℝ)^(offCount I)/L^2)*(∫ ξ,moments C d ξ ∂μ I)+
        ∫ ξ in (fullBand I (band L))ᶜ,‖mainDensity C ξ‖ ∂μ I) := by
  intro L d
  let S := fullBand I (band L)
  let F := weightedDifference C W N a b w L
  have hInt : Integrable F (μ I) := diff_integrable C W N a b hU w L
  have H :=
    integral_add_compl (fullBand_measurable (I:=I) (band L)) hInt
  have hD := integrate_difference C W N a b hU w R hR hP hχ
  have hE' : |∑ j : J,w j*(exactMain C W (a j) (b j) R-1)| =
      ‖(∫ ξ in S,F ξ ∂μ I)+(∫ ξ in Sᶜ,F ξ ∂μ I)‖ := by
    rw [H,hD,Complex.norm_real,Real.norm_eq_abs]
  rw [hE']
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact weighted_low C W N hW hWheel a b hU w hw hTotal L
      (Real.log_pos hR) δ E hδ hE hRef hC
  · exact high_weighted C W N hW a b hU w hw hTotal L hL

end ActualTZFiniteMainBand318
