module
public import IntegralInfinityChart318
public import IntegralSourceBranches318
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace IntegralValuativeRootCoordinates318
open Polynomial IntegralSourceBranches318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V K : Type*) [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

/-- A specified root in the specified fraction field descends unchanged to
its valuation ring when its square is integral. No sign is reselected. -/
theorem square_preimage (a : V) (z : K) (hz : z^2=algebraMap V K a) :
    ∃ w : V, algebraMap V K w=z ∧ w^2=a := by
  have hi : IsIntegral V z := by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [hz]
    exact isIntegral_algebraMap
  obtain ⟨w,hw⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  refine ⟨w,hw,IsFractionRing.injective V K ?_⟩
  rw [map_pow,hw,hz]

variable (c : Fin 4 → Vˣ) (t : K) (y : Fin 4 → K)
  (hy : ∀ i, (y i)^2=algebraMap V K (c i : V)*(t-algebraMap V K (contacts V i)))

include hy in
/-- The entire original affine point extends whenever its original t is
integral; all four original root signs are preserved. -/
theorem finite_coordinates (a : V) (ha : algebraMap V K a=t) :
    ∃ z : Fin 4 → V, (∀ i, algebraMap V K (z i)=y i) ∧
      ∀ i, (z i)^2=(c i : V)*(a-contacts V i) := by
  have h (i : Fin 4) : ∃ z : V, algebraMap V K z=y i ∧
      z^2=(c i : V)*(a-contacts V i) := by
    apply square_preimage V K
    rw [map_mul,map_sub,ha]
    exact hy i
  choose z hz hs using h
  exact ⟨z,hz,hs⟩

/-- In a local ring, the original reciprocal radicands are units whenever
u is a nonunit. This is the whole infinity neighborhood, not just u=0. -/
theorem infinity_denominator_unit (u : V) (hu : ¬IsUnit u) :
    IsUnit (Polynomial.eval u (IntegralInfinityChart318.denominator V c)) := by
  have hc (j : Fin 3) : IsUnit (Polynomial.eval u (IntegralInfinityChart318.coefficient V c j)) := by
    have hn : ¬IsUnit (IntegralInfinityChart318.contact V j * (↑(c 0)⁻¹ : V) * u^2) := by
      intro h
      exact hu ((isUnit_pow_iff (by decide : (2:ℕ)≠0)).mp (isUnit_of_mul_isUnit_right h))
    have h1 := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      (IntegralInfinityChart318.contact V j * (↑(c 0)⁻¹ : V) * u^2) hn
    simpa only [IntegralInfinityChart318.coefficient,Polynomial.eval_mul,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X] using
      ((c j.succ).isUnit.mul ((c 0)⁻¹).isUnit).mul h1
  simpa only [IntegralInfinityChart318.denominator,Polynomial.eval_prod] using
    IsUnit.prod_univ_iff.mpr hc

include hy in
/-- When the original t is not integral, the ACTUAL reciprocal coordinate
and all three ACTUAL signed ratios extend to the original infinity chart.
No replacement algebraic point or choice of square-root signs is used. -/
theorem infinity_coordinates (ht : ¬IsLocalization.IsInteger V t) :
    ∃ (u : V) (z : Fin 3 → V),
      algebraMap V K u=algebraMap V K (c 0 : V)/y 0 ∧
      (∀ j, algebraMap V K (z j)=y j.succ/y 0) ∧
      ¬IsUnit u ∧
      (∀ j, (z j)^2=Polynomial.eval u (IntegralInfinityChart318.coefficient V c j)) ∧
      IsUnit (Polynomial.eval u (IntegralInfinityChart318.denominator V c)) := by
  have ht0 : t≠0 := by intro h; exact ht ⟨0,by simpa only [map_zero] using h.symm⟩
  have hc0 : algebraMap V K (c 0 : V)≠0 := ((c 0).isUnit.map (algebraMap V K)).ne_zero
  have h0 : (y 0)^2=algebraMap V K (c 0 : V)*t := by
    simpa only [contacts,Matrix.cons_val_zero,map_zero,sub_zero] using hy 0
  have hy0 : y 0≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at h0
    exact mul_ne_zero hc0 ht0 h0.symm
  obtain ⟨s,hs⟩ := (ValuationRing.isInteger_or_isInteger V t).resolve_left ht
  have hsnu : ¬IsUnit s := by
    rintro ⟨v,hv⟩
    apply ht
    refine ⟨(↑v⁻¹ : V),?_⟩
    rw [map_units_inv,hv,hs,inv_inv]
  have hus : (algebraMap V K (c 0 : V)/y 0)^2=algebraMap V K ((c 0 : V)*s) := by
    rw [map_mul,hs,div_pow,h0]
    field_simp [hc0,ht0]
    <;> ring
  obtain ⟨u,hu,hu2⟩ := square_preimage V K ((c 0 : V)*s) _ hus
  have hun : ¬IsUnit u := by
    intro h
    have hh := h.pow 2
    rw [hu2] at hh
    exact hsnu (isUnit_of_mul_isUnit_right hh)
  have hr (j : Fin 3) : (y j.succ/y 0)^2=
      algebraMap V K (Polynomial.eval u (IntegralInfinityChart318.coefficient V c j)) := by
    have ha : contacts V j.succ=IntegralInfinityChart318.contact V j := by fin_cases j <;> rfl
    rw [div_pow,hy j.succ,h0,ha]
    simp only [IntegralInfinityChart318.coefficient,Polynomial.eval_mul,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
      map_mul,map_sub,map_one,map_pow,map_units_inv,hu,div_pow,h0]
    field_simp [hc0,ht0,hy0]
    <;> ring
  have he (j : Fin 3) : ∃ w : V, algebraMap V K w=y j.succ/y 0 ∧
      w^2=Polynomial.eval u (IntegralInfinityChart318.coefficient V c j) :=
    square_preimage V K _ _ (hr j)
  choose z hz hz2 using he
  exact ⟨u,z,hu,hz,hun,hz2,infinity_denominator_unit V c u hun⟩
end IntegralValuativeRootCoordinates318
