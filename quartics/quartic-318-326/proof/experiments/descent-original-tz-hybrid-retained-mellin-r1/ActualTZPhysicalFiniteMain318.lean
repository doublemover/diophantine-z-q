module
public import ActualTZFiniteChoiceIntegrand318
public import ActualTZMultiSieveCell318
import all ActualTZFiniteChoiceIntegrand318
import all ActualTZMellinFiniteGuard318
import all ActualTZMultiSieveCell318
import all ActualTZMultiDivisorExpansion318
import all ActualTZOneDivisorExpansion318
public section
noncomputable section
namespace ActualTZPhysicalFiniteMain318
open MeasureTheory
open scoped BigOperators ArithmeticFunction.Moebius
open ActualTZBooleanPrimeSlots318 ActualTZFiniteChoiceIntegrand318 ActualTZChoiceJointDensity318
open ActualTZMellinFiniteGuard318 ActualTZMellinKernel318 ActualTZLiteralSchwartz318
open ActualTZMultiSieveCell318 ActualTZMultiDivisorExpansion318 ActualTZOneDivisorExpansion318
open ActualTZMultiLinearCRT318

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem pair_injective (R : ℝ) :
    Function.Injective (fun q : Assignment I R×Assignment I R => paired q.1 q.2) := by
  intro x y h
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrFun h (i,true)
  · funext i
    apply Subtype.ext
    exact congrFun h (i,false)

private theorem digit_le (R : ℝ) (d : Digit R) : d.val≤⌊R⌋₊ :=
  (Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1).2

/-- The cutoff implicit in the original typed pair of assignments
is exactly the old floor-R cutoff on every slot of the image
table. In particular a squarefree digit equal to R is kept. -/
theorem table_cut_eq (P : ℕ) (R : ℝ) (hP : ⌊R⌋₊<P) :
    (digitTable I P).filter (fun d => ∀ j,d j≤⌊R⌋₊) =
      (Finset.univ : Finset (Assignment I R×Assignment I R)).image
        (fun q => paired q.1 q.2) := by
  classical
  ext d
  rw [Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨hd,hR⟩
    let take (s : Bool) : Assignment I R := fun i =>
      ⟨d (i,s),Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨table_pos P d hd _,hR (i,s)⟩,table_squarefree P d hd (i,s)⟩⟩
    refine ⟨(take true,take false),Finset.mem_univ _,?_⟩
    funext j
    rcases j with ⟨i,s⟩
    cases s <;> rfl
  · rintro ⟨⟨d,e⟩,_,rfl⟩
    have hR (j : Slot I) : paired d e j≤⌊R⌋₊ := by
      rcases j with ⟨i,s⟩
      cases s
      · exact digit_le R (e i)
      · exact digit_le R (d i)
    obtain ⟨x,hx⟩ := covers_cutoff P R hP (paired d e) (paired_squarefree d e) hR
    exact ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩,hR⟩

private theorem cut_term (C : Cutoff) (R : ℝ) (W : ℕ) (a : I→ℤ) (b : I→ℕ)
    (d e : Assignment I R) :
    crc W a b (paired d e)*
      (∏ j : Slot I,(C.χ (Real.log (paired d e j:ℝ)/Real.log R):ℂ)) =
    ((ActualTZMultiDivisorExpansion318.amplitude R C.χ d e*
      jointDensity W (paired d e) (a ∘ Prod.fst) (b ∘ Prod.fst):ℝ):ℂ) := by
  let v (j : Slot I) := (coeff R C.χ (paired d e j):ℂ)
  have hv (j : Slot I) : v j =
      ((μ (paired d e j):ℤ):ℂ)*
        (C.χ (Real.log (paired d e j:ℝ)/Real.log R):ℂ) := by
    simp only [v,coeff,Complex.ofReal_mul,Complex.ofReal_intCast]
  rw [crc]
  calc
    _ = (jointDensity W (paired d e) (a ∘ Prod.fst) (b ∘ Prod.fst):ℂ)*
        ∏ j : Slot I,v j := by
      simp only [hv,Finset.prod_mul_distrib] <;> ac_rfl
    _ = _ := by
      rw [Fintype.prod_prod_type]
      simp only [v,Fintype.prod_bool,paired,Bool.false_eq_true,if_false,if_true,
        Finset.prod_mul_distrib,ActualTZMultiDivisorExpansion318.amplitude,
        Complex.ofReal_mul,Complex.ofReal_prod] <;> ac_rfl

private theorem cutoff_to_old (C : Cutoff) (R : ℝ) (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hP : ⌊R⌋₊<P) :
    (∑ d∈(digitTable I P).filter (fun d => ∀ j,d j≤⌊R⌋₊),
      crc W a b d*(∏ j : Slot I,(C.χ (Real.log (d j:ℝ)/Real.log R):ℂ))) =
    ((∑ d : Assignment I R,∑ e : Assignment I R,
      ActualTZMultiDivisorExpansion318.amplitude R C.χ d e*
        jointDensity W (paired d e) (a ∘ Prod.fst) (b ∘ Prod.fst):ℝ):ℂ) := by
  classical
  rw [table_cut_eq P R hP,Finset.sum_image (pair_injective R).injOn,Fintype.sum_prod_type]
  simp only [Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun d _ =>
    Finset.sum_congr rfl (fun e _ => cut_term C R W a b d e))

/-- The ordinary exact finite main equals the angular integral of
the exact SIGNED finite prime product over the same original row.
No cutoff in frequency, no approximation, and no nonlinear
transference or prime-collision estimate is part of this theorem. -/
theorem finite_main_eq_integral (C : Cutoff) (R : ℝ) (hR : 1<R)
    (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (hP : ⌊R⌋₊<P) :
    (((((Nat.totient W:ℝ)/(W:ℝ))*Real.log R:ℝ):ℂ)^Fintype.card I) *
      (∫ ξ : Slot I→ℝ,
       (∏ j : Slot I,φ C (ξ j)) *
         (∏ p : PrimeAt P,∑ t : ActualTZLiteralAbsoluteEuler318.Pair I,
           ActualTZLiteralAbsoluteEuler318.entry W P a b (s1 (Real.log R) ξ)
               (s2 (Real.log R) ξ) p t)
       ∂ActualTZLiteralMellinTensor318.μ I) =
    (finiteMain ((Nat.totient W:ℝ)/(W:ℝ)) R C.χ W a b : ℂ) := by
  simp_rw [signed_prime_product,choice_integrand C W P a b hU]
  rw [physical_divisor_fubini C R hR W a b (digitTable I P) (table_pos P),
    cutoff_to_old C R W P a b hP]
  simp only [finiteMain,Complex.ofReal_mul,Complex.ofReal_pow]

end ActualTZPhysicalFiniteMain318
