module
public import ActualDuplicationPlaces318
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.Algebra.FiniteSupport.Basic
public section
namespace DuplicationFiniteProduct318
open ConcreteG8Domain LocalGenerator318 NumberField RelativeDuplicationHeight318 DuplicationProjective318
open Function
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

theorem actual_norm (x:K) : Algebra.norm ℚ x=AnchorNorm318.norm x := by
  rw [Algebra.norm_apply]
  exact QuadraticAlgebra.det_toLinearMap_eq_norm x

theorem coefficient_norm : Algebra.norm ℚ ((2:K)^3*D^2)=(392:ℚ)^2 := by
  rw [actual_norm,AnchorNorm318.norm_mul,AnchorNorm318.norm_pow,AnchorNorm318.norm_pow]
  norm_num [AnchorNorm318.norm,D,i,pair,QuadraticAlgebra.norm_def,pow_succ]

theorem coefficient_ne : (2:K)^3*D^2≠0 := by
  intro h
  have hn:=coefficient_norm
  rw [h,Algebra.norm_zero] at hn
  norm_num at hn

theorem finite_coefficient_product :
    (∏ᶠw:FinitePlace K,w (2:K)^3*w D^2)=1/(392:ℝ)^2 := by
  have he (w:FinitePlace K) : w (2:K)^3*w D^2=w ((2:K)^3*D^2) := by rw [map_mul,map_pow,map_pow]
  simp_rw [he]
  rw [FinitePlace.prod_eq_inv_abs_norm coefficient_ne,coefficient_norm]
  norm_num

theorem pair_finite_support (a b:K) (hab:a≠0 ∨ b≠0) :
    HasFiniteMulSupport (fun w:FinitePlace K=>max (w a) (w b)) := by
  by_cases ha:a=0
  · have hb:b≠0 := hab.resolve_left (not_not_intro ha)
    simpa [ha,max_eq_right (apply_nonneg _ _)] using FinitePlace.hasFiniteMulSupport hb
  by_cases hb:b=0
  · simpa [hb,max_eq_left (apply_nonneg _ _)] using FinitePlace.hasFiniteMulSupport ha
  exact (FinitePlace.hasFiniteMulSupport ha).max (FinitePlace.hasFiniteMulSupport hb)

theorem pair_ne_zero_of_function_ne_zero (x:Fin 2→K) (hx:x≠0) : x 0≠0 ∨ x 1≠0 := by
  by_contra hn
  have h0:x 0=0 := by tauto
  have h1:x 1=0 := by tauto
  apply hx
  funext i
  fin_cases i <;> simp [h0,h1]

@[expose] def finitePair (a b:K) : ℝ := ∏ᶠw:FinitePlace K,max (w a) (w b)

/-- All finite places are multiplied using their actual normalization.
The universal local loss gives exactly392² in the relative degree-two
height, without a PID, prime-classification or detached valuation premise. -/
theorem finite_forms_bounds (Q:E.Point) :
    (finitePair (Q.xRep 0) (Q.xRep 1))^4/(392:ℝ)^2≤
      finitePair (F (Q.xRep 0) (Q.xRep 1)) (G (Q.xRep 0) (Q.xRep 1)) ∧
    finitePair (F (Q.xRep 0) (Q.xRep 1)) (G (Q.xRep 0) (Q.xRep 1))≤
      (finitePair (Q.xRep 0) (Q.xRep 1))^4 := by
  let a:=Q.xRep 0
  let b:=Q.xRep 1
  have hm:=pair_finite_support a b (pair_ne_zero_of_function_ne_zero Q.xRep Q.xRep_ne_zero)
  have hf:forms Q≠0 := by
    obtain ⟨s,hs,he⟩:=forms_represent_double Q
    rw [he]
    exact smul_ne_zero hs ((2:ℤ) • Q).xRep_ne_zero
  have hfg:F a b≠0 ∨ G a b≠0 := by
    simpa [forms,a,b] using pair_ne_zero_of_function_ne_zero (forms Q) hf
  have ho:=pair_finite_support (F a b) (G a b) hfg
  have hc:HasFiniteMulSupport (fun w:FinitePlace K=>w (2:K)^3*w D^2) :=
    ((FinitePlace.hasFiniteMulSupport (by norm_num : (2:K)≠0)).pow 3).mul
      ((FinitePlace.hasFiniteMulSupport GlobalSquareHalving318.D_ne).pow 2)
  have hm4:HasFiniteMulSupport (fun w:FinitePlace K=>(max (w a) (w b))^4) := hm.pow 4
  have hlo:=finprod_le_finprod₀ (hc.mul hm4)
    (fun w:FinitePlace K=>mul_nonneg (mul_nonneg (pow_nonneg (apply_nonneg w _) 3)
      (sq_nonneg _)) (pow_nonneg ((apply_nonneg w a).trans (le_max_left _ _)) 4)) ho
    (fun w:FinitePlace K=>(ActualDuplicationPlaces318.finite_duplication_bounds w a b).1)
  have hup:=finprod_le_finprod₀ ho
    (fun w:FinitePlace K=>(apply_nonneg w (F a b)).trans (le_max_left _ _)) hm4
    (fun w:FinitePlace K=>(ActualDuplicationPlaces318.finite_duplication_bounds w a b).2)
  simp only [Pi.mul_apply] at hlo
  rw [finprod_mul_distrib hc hm4,finite_coefficient_product,←finprod_pow hm 4] at hlo
  rw [←finprod_pow hm 4] at hup
  constructor
  · simpa only [finitePair,a,b,div_eq_mul_inv,mul_comm,one_mul] using hlo
  · exact hup

end
end DuplicationFiniteProduct318
