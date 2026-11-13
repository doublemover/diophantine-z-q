module
public import ActualOriginalShiftedQuadraticMoment318
public section
noncomputable section
namespace ActualOriginalFiveQuadraticMoment318
open MeasureTheory ActualOriginalQuadraticFourthMoment318
open ActualOriginalQuadraticEnergyCount318 ActualOriginalShiftedQuadraticMoment318

lemma actual_four_product (a b c d : ℝ) : 4*(a*b*c*d)≤a^4+b^4+c^4+d^4 := by
  nlinarith only [sq_nonneg (a^2-b^2),sq_nonneg (c^2-d^2),sq_nonneg (a*b-c*d)]

lemma actual_five_norm_product (z0 z1 z2 z3 z4 : ℂ) (M : ℝ) (hM : 0≤M) (h4 : ‖z4‖≤M) :
    ‖z0*z1*z2*z3*z4‖≤(M/4)*(‖z0‖^4+‖z1‖^4+‖z2‖^4+‖z3‖^4) := by
  have hh := actual_four_product ‖z0‖ ‖z1‖ ‖z2‖ ‖z3‖
  have hm := mul_le_mul_of_nonneg_left hh (div_nonneg hM (by norm_num : (0 : ℝ)≤4))
  have hb := mul_le_mul_of_nonneg_left h4
    (show 0≤‖z0‖*‖z1‖*‖z2‖*‖z3‖ by positivity)
  simp only [norm_mul]
  nlinarith only [hm,hb]

/-- The genuine four-moment/one-supremum mechanism for five quadratic
factors. All four intervals may differ, all signed coefficients are kept,
and the fifth supremum is the ONLY cancellation input still supplied.
This does not yet identify an arbitrary weighted sum with the product. -/
theorem actual_five_quadratic_moment (H : ℕ) (s0 s1 s2 s3 s4 : Finset ℤ)
    (hs0 : s0⊆Finset.Icc (-(H : ℤ)) H) (hs1 : s1⊆Finset.Icc (-(H : ℤ)) H)
    (hs2 : s2⊆Finset.Icc (-(H : ℤ)) H) (hs3 : s3⊆Finset.Icc (-(H : ℤ)) H)
    (c0 c1 c2 c3 c4 : ℤ) (hc0 : c0≠0) (hc1 : c1≠0) (hc2 : c2≠0) (hc3 : c3≠0)
    (δ : ℝ) (hδ : 0<δ) (v : ℝ) (D : Set ℝ) (hDm : MeasurableSet D)
    (hD : D⊆Set.Ioc v (v+1)) (M : ℝ) (hM : 0≤M)
    (h4 : ∀ t∈D, ‖quadraticSum s4 c4 (t : AddCircle (1 : ℝ))‖≤M) :
    (∫ t in D, ‖quadraticSum s0 c0 (t : AddCircle (1 : ℝ))*
      quadraticSum s1 c1 (t : AddCircle (1 : ℝ))*quadraticSum s2 c2 (t : AddCircle (1 : ℝ))*
      quadraticSum s3 c3 (t : AddCircle (1 : ℝ))*quadraticSum s4 c4 (t : AddCircle (1 : ℝ))‖)≤
      M*momentBudget H δ := by
  let F (s : Finset ℤ) (c : ℤ) (t : ℝ) := ‖quadraticSum s c (t : AddCircle (1 : ℝ))‖^4
  have hi (s : Finset ℤ) (c : ℤ) : IntegrableOn (F s c) D :=
    (((actual_quadratic_continuous s c).norm.pow 4).continuousOn.integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self).mono_set hD
  have hp : IntegrableOn (fun t : ℝ => ‖quadraticSum s0 c0 (t : AddCircle (1 : ℝ))*
      quadraticSum s1 c1 (t : AddCircle (1 : ℝ))*quadraticSum s2 c2 (t : AddCircle (1 : ℝ))*
      quadraticSum s3 c3 (t : AddCircle (1 : ℝ))*quadraticSum s4 c4 (t : AddCircle (1 : ℝ))‖) D := by
    have hc := ((((actual_quadratic_continuous s0 c0).mul (actual_quadratic_continuous s1 c1)).mul
      (actual_quadratic_continuous s2 c2)).mul (actual_quadratic_continuous s3 c3)).mul
      (actual_quadratic_continuous s4 c4)
    exact (hc.norm.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).mono_set hD
  have hg := (((hi s0 c0).add (hi s1 c1)).add (hi s2 c2)).add (hi s3 c3)
  have hb := setIntegral_mono_on hp (hg.const_mul (M/4)) hDm
    (fun t ht => actual_five_norm_product _ _ _ _ _ M hM (h4 t ht))
  rw [integral_const_mul,integral_add (((hi s0 c0).add (hi s1 c1)).add (hi s2 c2)) (hi s3 c3),
    integral_add ((hi s0 c0).add (hi s1 c1)) (hi s2 c2),integral_add (hi s0 c0) (hi s1 c1)] at hb
  have h0 := actual_subset_quadratic_moment H s0 hs0 c0 hc0 δ hδ v D hD
  have h1 := actual_subset_quadratic_moment H s1 hs1 c1 hc1 δ hδ v D hD
  have h2 := actual_subset_quadratic_moment H s2 hs2 c2 hc2 δ hδ v D hD
  have h3 := actual_subset_quadratic_moment H s3 hs3 c3 hc3 δ hδ v D hD
  have hm := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add h0 h1) h2) h3)
    (div_nonneg hM (by norm_num : (0 : ℝ)≤4))
  dsimp [F] at hb
  nlinarith only [hb,hm]

end ActualOriginalFiveQuadraticMoment318
