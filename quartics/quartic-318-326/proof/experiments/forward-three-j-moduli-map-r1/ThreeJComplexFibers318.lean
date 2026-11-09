module
public import ThreeJActualFiniteOrders318
public import Mathlib.Algebra.Polynomial.Roots
public section
noncomputable section
namespace ThreeJComplexFibers318
open Polynomial ProjectiveLineFieldPoints318 ProjectiveLinePointEquiv318
open ProjectiveLineComplexTopology318 ThreeProjectiveJPoints318 ThreeJAnalyticGerms318
open ThreeCompactParameter318
set_option maxHeartbeats 600000

/-- The exact cleared finite-fiber equation, monic of degree four for every
complex target value. This does not define a new source or scheme map. -/
@[expose] def fiberPolynomial (c : ℂ) : ℂ[X] :=
  X^4+C (756-c)*X^3+C 196830*X^2+C 19131876*X+C 387420489

lemma fiberPolynomial_monic (c : ℂ) : (fiberPolynomial c).Monic := by
  unfold fiberPolynomial
  monicity!

lemma fiberPolynomial_degree (c : ℂ) : (fiberPolynomial c).natDegree=4 := by
  unfold fiberPolynomial
  compute_degree!

lemma fiberPolynomial_eval (c t : ℂ) :
    (fiberPolynomial c).eval t=finiteN t-c*t^3 := by
  simp only [fiberPolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_C]
  unfold finiteN
  ring

lemma root_ne_zero {c t : ℂ} (h : (fiberPolynomial c).IsRoot t) : t ≠ 0 := by
  intro ht
  subst t
  change (fiberPolynomial c).eval 0=0 at h
  rw [fiberPolynomial_eval,finiteN_zero] at h
  norm_num at h

lemma fiber_root_iff {c t : ℂ} (ht : t ≠ 0) :
    (fiberPolynomial c).IsRoot t ↔ J t=c := by
  change (fiberPolynomial c).eval t=0 ↔ J t=c
  rw [fiberPolynomial_eval,sub_eq_zero]
  exact (div_eq_iff (pow_ne_zero 3 ht)).symm

lemma finite_point_value {t : ℂ} (ht : t ≠ 0) :
    mapPoints (chartPoint (R:=ℚ) 1 t)=chartPoint (R:=ℚ) 1 (J t) := by
  have hd : aeval t ThreeProjectiveJCertificates318.finiteDenominator ≠ 0 := by
    rw [(finite_evaluations t).2]
    exact pow_ne_zero 3 ht
  rw [finite_formula t hd,←ActualThreeJChartConsumer318.finite_J]

/-- Exact equality between every genuine finite target fiber of the global
scheme-point action and the roots of its monic quartic fiber equation. -/
theorem finite_fiber_eq (c : ℂ) :
    {p : ComplexPoints | mapPoints p=chartPoint (R:=ℚ) 1 c} =
      chartPoint (R:=ℚ) 1 '' {t : ℂ | (fiberPolynomial c).IsRoot t} := by
  ext p
  constructor
  · intro hp
    rcases finite_or_infinity p with ⟨t,rfl⟩ | hpInf
    · have ht : t ≠ 0 := by
        intro ht
        subst t
        rw [finite_zero] at hp
        exact finite_ne_infinity c hp.symm
      refine ⟨t,(fiber_root_iff ht).mpr ?_,rfl⟩
      rw [finite_point_value ht] at hp
      exact chartPoint_injective 1 hp
    · rw [hpInf,reciprocal_zero] at hp
      exact (finite_ne_infinity c hp.symm).elim
  · rintro ⟨t,ht,rfl⟩
    rw [finite_point_value (root_ne_zero ht),(fiber_root_iff (root_ne_zero ht)).mp ht]

theorem finite_fiber_finite (c : ℂ) :
    Set.Finite {p : ComplexPoints | mapPoints p=chartPoint (R:=ℚ) 1 c} := by
  rw [finite_fiber_eq]
  exact (Polynomial.finite_setOfPred_isRoot (fiberPolynomial_monic c).ne_zero).image _

/-- The total multiplicity in the polynomial root multiset is bounded by4.
Together with finite_fiber_eq this supplies a concrete finite-fiber bound;
it is not yet the scheme morphism's finite/flat/degree theorem. -/
theorem fiber_root_count_le_four (c : ℂ) : (fiberPolynomial c).roots.card ≤ 4 := by
  simpa only [fiberPolynomial_degree] using Polynomial.card_roots' (fiberPolynomial c)

lemma infinity_fiber_subset :
    {p : ComplexPoints | mapPoints p=chartPoint (R:=ℚ) 0 (0:ℂ)} ⊆
      {chartPoint (R:=ℚ) 1 (0:ℂ),chartPoint (R:=ℚ) 0 (0:ℂ)} := by
  intro p hp
  rcases finite_or_infinity p with ⟨t,rfl⟩ | hpInf
  · by_cases ht : t=0
    · subst t
      exact Or.inl rfl
    · rw [finite_point_value ht] at hp
      exact (finite_ne_infinity (J t) hp).elim
  · exact Or.inr hpInf

/-- Every actual complex scheme-point fiber is finite, including target
infinity. Scheme-theoretic finiteness is deliberately a separate obligation. -/
theorem all_point_fibers_finite (p : ComplexPoints) : Set.Finite {q | mapPoints q=p} := by
  rcases finite_or_infinity p with ⟨c,rfl⟩ | hp
  · exact finite_fiber_finite c
  · rw [hp]
    exact (Set.finite_insert _ (Set.finite_singleton _)).subset infinity_fiber_subset

end ThreeJComplexFibers318
