module

public import SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
public import HolomorphicCharts318
import all SelectedMarkedPeriodCoordinate318
import all SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
import ActualJFinite318
import ActualJSurjective318
import Mathlib.Analysis.Analytic.Polynomial

public section
noncomputable section

open Filter Set Polynomial UpperHalfPlane
open scoped Polynomial Topology Manifold ContDiff nonZeroDivisors
open SelectedComplexOrdinaryBase318 SelectedActualComplexWholeRootField318
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318

namespace SelectedActualMarkedEllipticFieldContinuation318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open OpenJLocalComparison318 (j)

/-- Isolate any scalar value on the old upper-half-plane disk of the
actual fine quotient. This includes the critical values 0 and 1728,
without a nonzero first derivative assumption. -/
theorem eventually_j_ne_value (τ : UpperHalfPlane) (a : ℂ) :
    ∀ᶠ w in 𝓝[≠] (τ : ℂ), j w ≠ a := by
  by_cases ha : j (τ : ℂ) = a
  · obtain ⟨U,hU,hτ,hiso⟩ := ActualJFinite318.exists_isolating_open τ
    have hc : ContinuousAt UpperHalfPlane.ofComplex (τ : ℂ) :=
      (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) τ.im_pos).continuousAt
    have hτ' : UpperHalfPlane.ofComplex (τ : ℂ) ∈ U := by
      rwa [UpperHalfPlane.ofComplex_apply]
    have hclose : ∀ᶠ w in 𝓝 (τ : ℂ), UpperHalfPlane.ofComplex w ∈ U :=
      hc.eventually (hU.mem_nhds hτ')
    have hpos : ∀ᶠ w in 𝓝 (τ : ℂ), w ∈ UpperHalfPlane.upperHalfPlaneSet :=
      UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos
    filter_upwards [hclose.filter_mono nhdsWithin_le_nhds,
      hpos.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw hu hn
    intro h
    have h' : ActualQJ318.jInvariant (UpperHalfPlane.ofComplex w) = ActualQJ318.jInvariant τ := by
      change j w = ActualQJ318.jInvariant τ
      exact h.trans (ha.symm.trans
        (congrArg ActualQJ318.jInvariant (UpperHalfPlane.ofComplex_apply τ)))
    have hs : UpperHalfPlane.ofComplex w = τ := hiso _ hw h'
    have he := congrArg (fun q : UpperHalfPlane => (q : ℂ)) hs
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hu] at he
    exact (Set.mem_compl_iff.mp hn) (Set.mem_singleton_iff.mpr he)
  · exact ((OpenJLocalComparison318.j_analyticAt τ).continuousAt.eventually_ne ha).filter_mono
      nhdsWithin_le_nhds

theorem eventually_ordinary_in_punctured_period (τ : UpperHalfPlane) :
    ∀ᶠ w in 𝓝[≠] (τ : ℂ), OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex w) := by
  filter_upwards [eventually_j_ne_value τ 0,eventually_j_ne_value τ 1728] with w h₀ h₁
  exact ⟨h₀,h₁⟩

private theorem polynomial_analytic (τ : UpperHalfPlane) (a : ℂ[X]) :
    AnalyticAt ℂ (fun w => a.eval (j w)) (τ : ℂ) := by
  have ha : AnalyticAt ℂ (fun w : ℂ => a.eval w) (j (τ : ℂ)) :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) a) _ (Set.mem_univ _)
  exact ha.comp (OpenJLocalComparison318.j_analyticAt τ)

private theorem polynomial_not_zero_punctured (τ : UpperHalfPlane) (a : ℂ[X]) (ha : a ≠ 0) :
    ∀ᶠ w in 𝓝[≠] (τ : ℂ), a.eval (j w) ≠ 0 := by
  let T : Set ℂ := {w | a.eval w = 0}
  letI : Finite T := (Polynomial.finite_setOfPred_isRoot ha).to_subtype
  have h (z : T) : ∀ᶠ w in 𝓝[≠] (τ : ℂ), j w ≠ z.val :=
    eventually_j_ne_value τ z
  have hf : ∀ᶠ w in 𝓝[≠] (τ : ℂ), ∀ z : T, j w ≠ z.val := Filter.eventually_all.mpr h
  exact hf.mono fun w h he => h ⟨j w,he⟩ rfl

private theorem scale_meromorphic (τ : UpperHalfPlane) :
    MeromorphicAt CanonicalXScale318.scale (τ : ℂ) := by
  have hj := (OpenJLocalComparison318.j_analyticAt τ).meromorphicAt
  have hs := hj.fun_sub (MeromorphicAt.const (1728 : ℂ) (τ : ℂ))
  have hA : MeromorphicAt OpenJLocalComparison318.A (τ : ℂ) :=
    ((MeromorphicAt.const (-3 : ℂ) (τ : ℂ)).fun_mul hj).fun_mul hs.fun_inv
  have hB : MeromorphicAt OpenJLocalComparison318.B (τ : ℂ) :=
    ((MeromorphicAt.const (-2 : ℂ) (τ : ℂ)).fun_mul hj).fun_mul hs.fun_inv
  have hE4 : AnalyticAt ℂ (fun z => ModularForm.E₄ (UpperHalfPlane.ofComplex z)) (τ : ℂ) := by
    exact (UpperHalfPlane.mdifferentiable_iff.mp
      (ModularForm.E (k:=4) (by norm_num)).holo').analyticOnNhd
        UpperHalfPlane.isOpen_upperHalfPlaneSet τ τ.im_pos
  have hE6 : AnalyticAt ℂ (fun z => ModularForm.E₆ (UpperHalfPlane.ofComplex z)) (τ : ℂ) := by
    exact (UpperHalfPlane.mdifferentiable_iff.mp
      (ModularForm.E (k:=6) (by norm_num)).holo').analyticOnNhd
        UpperHalfPlane.isOpen_upperHalfPlaneSet τ τ.im_pos
  have hC : AnalyticAt ℂ OpenJLocalComparison318.C (τ : ℂ) := hE4.neg.div_const
  have hD : AnalyticAt ℂ OpenJLocalComparison318.D (τ : ℂ) := hE6.neg.div_const
  change MeromorphicAt (fun z =>
    (OpenJLocalComparison318.D z / OpenJLocalComparison318.B z) /
    (OpenJLocalComparison318.C z / OpenJLocalComparison318.A z)) (τ : ℂ)
  exact (hD.meromorphicAt.fun_div hB).fun_div (hC.meromorphicAt.fun_div hA)

variable (N : ℕ) [NeZero N]

/-- The identical marked abscissa used by the whole original polynomial
extends meromorphically across the omitted finite values. Its unscaled
lattice series is holomorphic at every true upper-half-plane period. -/
theorem marked_root_meromorphic_at_interior (hN : 1 < N) (τ : UpperHalfPlane) :
    MeromorphicAt (fun w => SelectedMarkedPeriodCoordinate318.arithmeticX N
      (UpperHalfPlane.ofComplex w)) (τ : ℂ) := by
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have ha : ‖((N : ℂ)⁻¹)‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast,← one_div]
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (N : ℝ))).mpr
    simpa only [one_mul] using hNR
  have hw :=
    (SelectedMarkedPeriodCoordinate318.wp_analyticAt ((N : ℂ)⁻¹) ha
      (SelectedMarkedPeriodCoordinate318.marker_not_lattice N hN) τ).div_const
        (c := (2*(Real.pi:ℂ))^2)
  have he : (fun w : ℂ => SelectedMarkedPeriodCoordinate318.arithmeticX N
      (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 (τ : ℂ)]
      (fun w : ℂ => ((PeriodEisenstein318.periods (UpperHalfPlane.ofComplex w)).weierstrassP
        ((N : ℂ)⁻¹)/(2*(Real.pi : ℂ))^2)/CanonicalXScale318.scale w) := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    change SelectedMarkedPeriodCoordinate318.arithmeticX N
      (UpperHalfPlane.ofComplex (↑(⟨w,hw⟩ : UpperHalfPlane) : ℂ)) = _
    rw [UpperHalfPlane.ofComplex_apply]
    exact SelectedMarkedPeriodCoordinate318.arithmeticX_formula N hN ⟨w,hw⟩
  exact (hw.meromorphicAt.fun_div (scale_meromorphic τ)).congr
    ((he.filter_mono nhdsWithin_le_nhds).symm)

variable (p : (OpenJModel318.Base N)[X])
variable (hRoots : fullRootSet N p) (t : Period)

private theorem polynomial_at_admissible (w : ℂ)
    (hw : OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex w))
    (a : ℂ[X]) :
    atDisk N p hRoots t w (AdjoinRoot.of (pC N p) (algebraMap ℂ[X] Base a)) =
      a.eval (j w) := by
  rw [atDisk_of_admissible N p hRoots t w hw,atPeriod_base]
  exact evaluation_polynomial _ a

private theorem base_eq_fraction_punctured (τ : UpperHalfPlane)
    (b : Base) (a : ℂ[X]) (d : Submonoid.powers denominator)
    (he : b * algebraMap ℂ[X] Base (d : ℂ[X]) = algebraMap ℂ[X] Base a) :
    (fun w => atDisk N p hRoots t w (AdjoinRoot.of (pC N p) b)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun w => a.eval (j w) / d.val.eval (j w) := by
  filter_upwards [eventually_ordinary_in_punctured_period τ] with w hw
  let χ := (atDisk N p hRoots t w).comp (AdjoinRoot.of (pC N p))
  have hd : χ (algebraMap ℂ[X] Base (d : ℂ[X])) = d.val.eval (j w) :=
    polynomial_at_admissible N p hRoots t w hw d
  have hd' : χ (algebraMap ℂ[X] Base (d : ℂ[X])) ≠ 0 :=
    ((IsLocalization.map_units Base d).map χ).ne_zero
  have hmul := congrArg χ he
  change χ (b * algebraMap ℂ[X] Base (d : ℂ[X])) = χ (algebraMap ℂ[X] Base a) at hmul
  rw [map_mul,hd] at hmul
  exact (eq_div_iff (fun h => hd' (hd.trans h))).mpr
    (hmul.trans (polynomial_at_admissible N p hRoots t w hw a))

private theorem base_meromorphic (τ : UpperHalfPlane) (b : Base) :
    MeromorphicAt (fun w => atDisk N p hRoots t w (AdjoinRoot.of (pC N p) b)) (τ : ℂ) := by
  obtain ⟨⟨a,d⟩,he⟩ := IsLocalization.surj (Submonoid.powers denominator) b
  exact ((polynomial_analytic τ a).meromorphicAt.fun_div
    (polynomial_analytic τ d).meromorphicAt).congr
    (base_eq_fraction_punctured N p hRoots t τ b a d he).symm

private theorem base_not_zero (τ : UpperHalfPlane) (b : Base) (hb : b ≠ 0) :
    ∀ᶠ w in 𝓝[≠] (τ : ℂ),
      atDisk N p hRoots t w (AdjoinRoot.of (pC N p) b) ≠ 0 := by
  letI : IsDomain Base := coefficient_domain
  obtain ⟨⟨a,d⟩,he⟩ := IsLocalization.surj (Submonoid.powers denominator) b
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,map_zero] at he
    exact hb ((mul_eq_zero.mp he).resolve_right (IsLocalization.map_units Base d).ne_zero)
  filter_upwards [base_eq_fraction_punctured N p hRoots t τ b a d he,
    polynomial_not_zero_punctured τ a ha,eventually_ordinary_in_punctured_period τ] with w hw hna hadm
  have hn : d.val.eval (j w) ≠ 0 := by
    rw [← polynomial_at_admissible N p hRoots t w hadm]
    exact (((IsLocalization.map_units Base d).map (AdjoinRoot.of (pC N p))).map
      (atDisk N p hRoots t w)).ne_zero
  rw [hw]
  exact div_ne_zero hna hn

private theorem root_meromorphic (hN : 1 < N) (τ : UpperHalfPlane) :
    MeromorphicAt (fun w => atDisk N p hRoots t w (AdjoinRoot.root (pC N p))) (τ : ℂ) := by
  apply (marked_root_meromorphic_at_interior N hN τ).congr
  filter_upwards [eventually_ordinary_in_punctured_period τ] with w hw
  rw [atDisk_of_admissible N p hRoots t w hw,atPeriod_root]

private theorem section_meromorphic (hN : 1 < N) (τ : UpperHalfPlane) (r : OrdinaryRoot N p) :
    MeromorphicAt (fun w => atDisk N p hRoots t w r) (τ : ℂ) := by
  refine AdjoinRoot.induction_on (pC N p) r fun f => ?_
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
    have he : (fun w => atDisk N p hRoots t w (AdjoinRoot.mk (pC N p) (f + g))) =
        (fun w => atDisk N p hRoots t w (AdjoinRoot.mk (pC N p) f) +
          atDisk N p hRoots t w (AdjoinRoot.mk (pC N p) g)) := by
      funext w
      simp only [map_add]
    rw [he]
    exact hf.fun_add hg
  | monomial n a =>
    have he : (fun w => atDisk N p hRoots t w (AdjoinRoot.mk (pC N p) (monomial n a))) =
        (fun w => atDisk N p hRoots t w (AdjoinRoot.of (pC N p) a) *
          (atDisk N p hRoots t w (AdjoinRoot.root (pC N p))) ^ n) := by
      funext w
      simp only [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
        AdjoinRoot.mk_C,AdjoinRoot.mk_X] <;> rfl
    rw [he]
    exact (base_meromorphic N p hRoots t τ a).fun_mul
      ((root_meromorphic N p hRoots t hN τ).fun_pow n)

private theorem exists_ordinary_seed : Nonempty Period := by
  obtain ⟨σ,hσ⟩ := ActualJSurjective318.surjective (1 : ℂ)
  refine ⟨⟨σ,?_⟩⟩
  change ActualQJ318.jInvariant σ ≠ 0 ∧ ActualQJ318.jInvariant σ ≠ 1728
  rw [hσ]
  norm_num

/-- At any old fine-quotient chart, including either omitted elliptic
value, an arbitrary element of the original installed whole field has
a meromorphic representative extending the identical marked ordinary
evaluation on the puncture. The inverse of the actual chart is precisely
the fine quotient projection of the periods used in this formula. -/
theorem whole_field_meromorphic_at_finite_branch
    (hN : 5 ≤ N) (τ : UpperHalfPlane) (h : K N p) :
    ∃ (t : Period) (b : Base) (r : OrdinaryRoot N p),
      let s := AdjoinRoot.of (pC N p) b
      b ≠ 0 ∧ h * intoWhole N p s = intoWhole N p r ∧
      (∀ᶠ w in 𝓝[≠] (τ : ℂ),
        OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex w) ∧
        (HolomorphicCharts318.localChart N hN τ).symm w =
          GammaOneAtlas318.quotientMap N (UpperHalfPlane.ofComplex w) ∧
        atDisk N p hRoots t w s ≠ 0) ∧
      MeromorphicAt (fun w => atDisk N p hRoots t w r / atDisk N p hRoots t w s) (τ : ℂ) := by
  obtain ⟨t⟩ := exists_ordinary_seed
  obtain ⟨b,hb,r,hr⟩ := clear_in_whole N p h
  have hN' : 1 < N := by omega
  refine ⟨t,b,r,hb,hr,?_, (section_meromorphic N p hRoots t hN' τ r).fun_div
    (base_meromorphic N p hRoots t τ b)⟩
  filter_upwards [eventually_ordinary_in_punctured_period τ,
    base_not_zero N p hRoots t τ b hb] with w hw hn
  exact ⟨hw,HolomorphicCharts318.localChart_symm_apply N hN τ w,hn⟩

/-- Independence of the polynomial denominator, numerator and irrelevant
fallback period over the identical marked puncture. No nonvanishing
derivative at the omitted value is used. -/
theorem whole_field_finite_branch_same_germ (hp : p.Monic) (τ : UpperHalfPlane)
    (t' : Period) (h : K N p) (b d : Base) (r s : OrdinaryRoot N p)
    (hb : b ≠ 0) (hd : d ≠ 0)
    (hr : h * intoWhole N p (AdjoinRoot.of (pC N p) b) = intoWhole N p r)
    (hs : h * intoWhole N p (AdjoinRoot.of (pC N p) d) = intoWhole N p s) :
    (fun w => atDisk N p hRoots t w r /
      atDisk N p hRoots t w (AdjoinRoot.of (pC N p) b)) =ᶠ[𝓝[≠] (τ : ℂ)]
    (fun w => atDisk N p hRoots t' w s /
      atDisk N p hRoots t' w (AdjoinRoot.of (pC N p) d)) := by
  have he : r * AdjoinRoot.of (pC N p) d = s * AdjoinRoot.of (pC N p) b := by
    apply intoWhole_injective N p hp
    rw [map_mul,map_mul,← hr,← hs,mul_assoc,mul_assoc]
    exact congrArg (fun a : K N p => h * a) (mul_comm _ _)
  filter_upwards [base_not_zero N p hRoots t τ b hb,base_not_zero N p hRoots t τ d hd,
    eventually_ordinary_in_punctured_period τ] with w hbw hdw hw
  have hEval : atDisk N p hRoots t' w = atDisk N p hRoots t w := by
    rw [atDisk_of_admissible N p hRoots t' w hw,atDisk_of_admissible N p hRoots t w hw]
  rw [hEval]
  apply (div_eq_div_iff hbw hdw).mpr
  simpa only [map_mul] using
    congrArg (fun a : OrdinaryRoot N p => atDisk N p hRoots t w a) he

end SelectedActualMarkedEllipticFieldContinuation318

#print axioms SelectedActualMarkedEllipticFieldContinuation318.marked_root_meromorphic_at_interior
#print axioms SelectedActualMarkedEllipticFieldContinuation318.whole_field_meromorphic_at_finite_branch
#print axioms SelectedActualMarkedEllipticFieldContinuation318.whole_field_finite_branch_same_germ
