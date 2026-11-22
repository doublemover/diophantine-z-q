module

public import SelectedActualMarkedCuspPunctureEvaluation318
public import Mathlib.Order.Filter.Germ.Basic
import all SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
import Mathlib.RingTheory.Localization.Defs

public section
noncomputable section

open Filter Set Polynomial
open scoped Polynomial Topology nonZeroDivisors
open FiniteCuspEnds318
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedCuspPunctureEvaluation318

namespace SelectedActualMarkedCuspWholeField318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N : ℕ) [NeZero N] (hN : 5 ≤ N) (c : End N)
variable (p : (OpenJModel318.Base N)[X]) (hRoots : fullRootSet N p)
variable (t : Period)

/-- Germs on the true puncture; no local limit or analytic order was
put into the ring type. -/
abbrev Germ0 := Germ (𝓝[≠] (0 : ℂ)) ℂ

private theorem eventually_cuspJ_norm_gt (M : ℝ) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ),
      M < ‖AllCuspJPole318.localJ (AllCuspQJ318.natWidth N hN c) q‖ := by
  obtain ⟨δ,hδ,h⟩ := AllCuspQJ318.small_parameter_large_j N hN c M
  have hd : Metric.ball (0 : ℂ) δ ∈ 𝓝[≠] (0 : ℂ) :=
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ)) (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hd,self_mem_nhdsWithin] with q hq hn
  exact h q (by simpa only [Metric.mem_ball,dist_zero_right] using hq)
    (fun e => hn (Set.mem_singleton_iff.mpr e))

theorem nonzero_cusp_polynomial (a : ℂ[X]) (ha : a ≠ 0) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ),
      a.eval (AllCuspJPole318.localJ (AllCuspQJ318.natWidth N hN c) q) ≠ 0 := by
  let Z : Set ℂ := {z | a.eval z = 0}
  have hFin : Z.Finite := Polynomial.finite_setOfPred_isRoot ha
  obtain ⟨M,hM⟩ := (hFin.image (fun z : ℂ => ‖z‖)).bddAbove
  filter_upwards [eventually_cuspJ_norm_gt N hN c M] with q hq
  intro hz
  exact (not_lt_of_ge (hM (mem_image_of_mem _ (show _ ∈ Z from hz)))) hq

/-- A genuinely nonzero element of the original localized coefficient
ring stays nonzero on a smaller actual cusp puncture. -/
theorem nonzero_cusp_base (b : Base) (hb : b ≠ 0) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), atCusp N hN c p hRoots t q (AdjoinRoot.of (pC N p) b) ≠ 0 := by
  letI : IsDomain Base := coefficient_domain
  obtain ⟨⟨a,d⟩,he⟩ := IsLocalization.surj (Submonoid.powers denominator) b
  have ha : a ≠ 0 := by
    intro hz
    rw [hz,map_zero] at he
    exact hb ((mul_eq_zero.mp he).resolve_right (IsLocalization.map_units Base d).ne_zero)
  filter_upwards [nonzero_cusp_polynomial N hN c a ha,
    original_cusp_polynomial_evaluation N hN c p hRoots t a] with q hq hEval
  let E := (atCusp N hN c p hRoots t q).comp (AdjoinRoot.of (pC N p))
  have hProd := congrArg E he
  change E (b * algebraMap ℂ[X] Base (d : ℂ[X])) = E (algebraMap ℂ[X] Base a) at hProd
  rw [map_mul] at hProd
  change E b ≠ 0
  intro hz
  rw [hz,zero_mul] at hProd
  exact hq (hEval.symm.trans hProd.symm)

/-- Bundle pointwise evaluations, then pass to the punctured germ. -/
def cuspSectionEval : OrdinaryRoot N p →+* Germ0 :=
  (Germ.coeRingHom (𝓝[≠] (0 : ℂ))).comp
    { toFun := fun z q => atCusp N hN c p hRoots t q z
      map_one' := funext (fun q => map_one (atCusp N hN c p hRoots t q))
      map_zero' := funext (fun q => map_zero (atCusp N hN c p hRoots t q))
      map_add' u v := funext (fun q => map_add (atCusp N hN c p hRoots t q) u v)
      map_mul' u v := funext (fun q => map_mul (atCusp N hN c p hRoots t q) u v) }

theorem cuspSectionEval_apply (z : OrdinaryRoot N p) :
    cuspSectionEval N hN c p hRoots t z =
      Germ.ofFun (fun q => atCusp N hN c p hRoots t q z) := by
  rfl

private theorem section_denominator_unit (b : Base) (hb : b ≠ 0) :
    IsUnit (cuspSectionEval N hN c p hRoots t (AdjoinRoot.of (pC N p) b)) := by
  let f := fun q => atCusp N hN c p hRoots t q (AdjoinRoot.of (pC N p) b)
  let v : Germ0 := Germ.ofFun (fun q => (f q)⁻¹)
  have hv : cuspSectionEval N hN c p hRoots t (AdjoinRoot.of (pC N p) b) * v = 1 := by
    rw [cuspSectionEval_apply]
    change Germ.ofFun (fun q => f q * (f q)⁻¹) = Germ.ofFun (fun _ => (1 : ℂ))
    apply Germ.coe_eq.mpr
    exact (nonzero_cusp_base N hN c p hRoots t b hb).mono
      (fun q hq => mul_inv_cancel₀ hq)
  exact ⟨Units.mkOfMulEqOne _ v hv,rfl⟩

private abbrev S := (nonZeroDivisors Base).map (AdjoinRoot.of (pC N p)).toMonoidHom

include hN c hRoots t in
private theorem whole_is_section_localization
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p))) :
    letI : Field (K N p) := (whole_isField N p hf).toField
    letI : Algebra (OrdinaryRoot N p) (K N p) := (intoWhole N p).toAlgebra
    IsLocalization (S N p) (K N p) := by
  letI : Field (K N p) := (whole_isField N p hf).toField
  letI : Algebra (OrdinaryRoot N p) (K N p) := (intoWhole N p).toAlgebra
  letI : IsDomain Base := coefficient_domain
  apply (isLocalization_iff (S N p) (K N p)).mpr
  refine ⟨?_,?_,?_⟩
  · rintro ⟨_,b,hb,rfl⟩
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have h0 : intoWhole N p (AdjoinRoot.of (pC N p) b) = 0 := hz
    have hz' : AdjoinRoot.of (pC N p) b = 0 :=
      intoWhole_injective N p hp (h0.trans (map_zero (intoWhole N p)).symm)
    obtain ⟨q,hq⟩ := (nonzero_cusp_base N hN c p hRoots t b
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)).exists
    exact hq (by rw [hz',map_zero])
  · intro x
    obtain ⟨b,hb,r,hr⟩ := clear_in_whole N p x
    exact ⟨⟨r,⟨AdjoinRoot.of (pC N p) b,b,mem_nonZeroDivisors_iff_ne_zero.mpr hb,rfl⟩⟩,hr⟩
  · intro x y h
    have he : x = y := intoWhole_injective N p hp h
    exact ⟨1,by rw [he]⟩

/-- The entire original field, mapped into germs on this exact original
filled cusp puncture. Its restriction is the actual marked evaluation;
every element has an original polynomial-denominator formula analytic
on a sufficiently small punctured neighborhood. -/
theorem actual_whole_cusp_germ
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p))) :
    letI : Field (K N p) := (whole_isField N p hf).toField
    ∃ E : K N p →+* Germ0,
      Function.Injective E ∧
      (∀ z : OrdinaryRoot N p, E (intoWhole N p z) =
        Germ.ofFun (fun q => atCusp N hN c p hRoots t q z)) ∧
      ∀ x : K N p, ∃ f : ℂ → ℂ, E x = Germ.ofFun f ∧
        (∀ᶠ q in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ f q) := by
  letI : Field (K N p) := (whole_isField N p hf).toField
  letI : Algebra (OrdinaryRoot N p) (K N p) := (intoWhole N p).toAlgebra
  letI : IsDomain Base := coefficient_domain
  letI : IsLocalization (S N p) (K N p) := whole_is_section_localization N hN c p hRoots t hp hf
  let ψ := cuspSectionEval N hN c p hRoots t
  have hU : ∀ s : S N p, IsUnit (ψ s) := by
    rintro ⟨_,b,hb,rfl⟩
    exact section_denominator_unit N hN c p hRoots t b (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  let E : K N p →+* Germ0 := IsLocalization.lift (g := ψ) hU
  have hE (z : OrdinaryRoot N p) : E (intoWhole N p z) = ψ z :=
    IsLocalization.lift_eq hU z
  refine ⟨E,E.injective,fun z => (hE z).trans (cuspSectionEval_apply N hN c p hRoots t z),?_⟩
  intro x
  obtain ⟨b,hb,r,hr⟩ := clear_in_whole N p x
  let s := AdjoinRoot.of (pC N p) b
  let f := fun q => atCusp N hN c p hRoots t q r / atCusp N hN c p hRoots t q s
  have hDen := nonzero_cusp_base N hN c p hRoots t b hb
  have hx : E x * ψ s = ψ r := by
    have h : E (x * intoWhole N p s) = E (intoWhole N p r) := congrArg E hr
    rw [map_mul,hE s,hE r] at h
    exact h
  have hf : Germ.ofFun f * ψ s = ψ r := by
    rw [show ψ s = Germ.ofFun (fun q => atCusp N hN c p hRoots t q s) from
      cuspSectionEval_apply N hN c p hRoots t s,
      show ψ r = Germ.ofFun (fun q => atCusp N hN c p hRoots t q r) from
      cuspSectionEval_apply N hN c p hRoots t r]
    change Germ.ofFun (fun q => f q * atCusp N hN c p hRoots t q s) =
      Germ.ofFun (fun q => atCusp N hN c p hRoots t q r)
    apply Germ.coe_eq.mpr
    exact hDen.mono (fun q hq => div_mul_cancel₀ _ hq)
  refine ⟨f,(IsUnit.mul_left_inj (section_denominator_unit N hN c p hRoots t b hb)).mp
    (hx.trans hf.symm),?_⟩
  filter_upwards [eventually_ordinary_at_original_cusp N hN c,hDen] with q hq hd
  exact (original_cusp_ordinary_section_analytic N hN c p hRoots t q hq.1 hq.2 r).fun_div
    (original_cusp_ordinary_section_analytic N hN c p hRoots t q hq.1 hq.2 s) hd

end SelectedActualMarkedCuspWholeField318

#print axioms SelectedActualMarkedCuspWholeField318.actual_whole_cusp_germ
