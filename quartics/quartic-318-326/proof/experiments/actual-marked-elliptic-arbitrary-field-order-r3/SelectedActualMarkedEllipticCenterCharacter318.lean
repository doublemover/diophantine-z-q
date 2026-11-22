module

public import SelectedActualLiteralMarkedOrdinaryNormalization318
public import SelectedActualMarkedEllipticFieldContinuation318
import all SelectedActualMarkedEllipticFieldContinuation318
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

public section
noncomputable section

open Filter Set Polynomial
open scoped Polynomial Topology TensorProduct
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexGenericChartClosures318
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra literalWholeTensor)
open SelectedActualLiteralMarkedOrdinaryNormalization318 (B O actual_literal_ordinary_normalization)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedEllipticFieldContinuation318
open OpenJLocalComparison318 (j)

namespace SelectedActualMarkedEllipticCenterCharacter318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem continuous_eval₂_along_polynomial_base (P : ℂ[X][X]) :
    Continuous (fun w : ℂ × ℂ => P.eval₂ (Polynomial.evalRingHom w.1) w.2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have he : (fun w : ℂ × ℂ => (P + Q).eval₂ (Polynomial.evalRingHom w.1) w.2) =
        (fun w => P.eval₂ (Polynomial.evalRingHom w.1) w.2) +
        (fun w => Q.eval₂ (Polynomial.evalRingHom w.1) w.2) := by
      funext w
      rw [Pi.add_apply, Polynomial.eval₂_add]
    rw [he]
    exact hP.add hQ
  | monomial n a =>
    let b : ℂ × ℂ → ℂ := (fun v : ℂ => a.eval v) ∘ Prod.fst
    have he : (fun w : ℂ × ℂ => (Polynomial.monomial n a).eval₂
        (Polynomial.evalRingHom w.1) w.2) = b * (Prod.snd : ℂ × ℂ → ℂ)^n := by
      funext w
      rw [Pi.mul_apply, Pi.pow_apply, Polynomial.eval₂_monomial] <;> rfl
    rw [he]
    exact ((Polynomial.continuous a).comp continuous_fst).mul (continuous_snd.pow n)

/-- A pole would make the leading monic term have strictly least order.
Reversing the polynomial is exactly division through by that term:
the remaining powers of the inverse vanish at the center. -/
private theorem nonnegative_from_monic_relation
    (τ : UpperHalfPlane) (f : ℂ → ℂ) (hf : MeromorphicAt f (τ : ℂ))
    (P : ℂ[X][X]) (hP : P.Monic)
    (hRoot : ∀ᶠ w in 𝓝[≠] (τ : ℂ), P.eval₂ (Polynomial.evalRingHom (j w)) (f w) = 0) :
    0 ≤ meromorphicOrderAt f (τ : ℂ) := by
  by_contra! hneg
  have hfinite : meromorphicOrderAt f (τ : ℂ) ≠ ⊤ :=
    ne_of_lt (hneg.trans_le le_top)
  have hne : ∀ᶠ w in 𝓝[≠] (τ : ℂ), f w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp hfinite
  have hinf : Tendsto f (𝓝[≠] (τ : ℂ)) (Bornology.cobounded ℂ) :=
    tendsto_cobounded_of_meromorphicOrderAt_neg hneg
  have hinv : Tendsto (fun w => (f w)⁻¹) (𝓝[≠] (τ : ℂ)) (𝓝 (0 : ℂ)) :=
    Filter.tendsto_inv₀_cobounded.comp hinf
  have hJ : Tendsto j (𝓝[≠] (τ : ℂ)) (𝓝 (j (τ : ℂ))) :=
    (OpenJLocalComparison318.j_analyticAt τ).continuousAt.continuousWithinAt.tendsto
  let E := fun w : ℂ => P.reverse.eval₂ (Polynomial.evalRingHom (j w)) (f w)⁻¹
  have hE : E =ᶠ[𝓝[≠] (τ : ℂ)] fun _ => 0 := by
    filter_upwards [hne,hRoot] with w hw hroot
    letI : Invertible (f w) := invertibleOfNonzero hw
    change P.reverse.eval₂ (Polynomial.evalRingHom (j w)) (f w)⁻¹ = 0
    rw [← invOf_eq_inv]
    exact (Polynomial.eval₂_reverse_eq_zero_iff (Polynomial.evalRingHom (j w)) (f w) P).mpr hroot
  have h0 : Tendsto E (𝓝[≠] (τ : ℂ)) (𝓝 (0 : ℂ)) :=
    tendsto_const_nhds.congr' hE.symm
  have hb : P.reverse.eval₂ (Polynomial.evalRingHom (j (τ : ℂ))) 0 = 1 := by
    rw [Polynomial.eval₂_at_zero, Polynomial.coeff_zero_reverse, hP.leadingCoeff, map_one]
  have hC : ContinuousAt
      (fun w : ℂ × ℂ => P.reverse.eval₂ (Polynomial.evalRingHom w.1) w.2)
      (j (τ : ℂ), (0 : ℂ)) := (continuous_eval₂_along_polynomial_base P.reverse).continuousAt
  have hh := hC.tendsto.comp (hJ.prodMk_nhds hinv)
  have h1 : Tendsto E (𝓝[≠] (τ : ℂ)) (𝓝 (1 : ℂ)) := by
    change Tendsto E (𝓝[≠] (τ : ℂ)) (𝓝
      (P.reverse.eval₂ (Polynomial.evalRingHom (j (τ : ℂ))) 0)) at hh
    exact hb ▸ hh
  exact zero_ne_one (tendsto_nhds_unique h0 h1)

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hRoots : fullRootSet N p)

variable {F : Type} [Field F] [Algebra JField F]

/-- The old ordinary evaluation of actual compact integral sections on
the genuine marked puncture. The comparison e is the whole principal
normalization isomorphism, not an independently chosen local character. -/
def puncturedChartEvaluation (t : Period) (e : OrdinaryRoot N p ≃ₐ[Base] O F) (w : ℂ) :
    B F →+* ℂ :=
  (atDisk N p hRoots t w).comp (e.symm.toRingHom.comp (algebraMap (B F) (O F)))

private theorem chart_polynomial_evaluation
    (t : Period) (e : OrdinaryRoot N p ≃ₐ[Base] O F) (w : ℂ)
    (hw : OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex w)) :
    (puncturedChartEvaluation N p hRoots t e w).comp (algebraMap ℂ[X] (B F)) =
      Polynomial.evalRingHom (j w) := by
  apply RingHom.ext
  intro a
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  have hB : algebraMap (B F) (O F) (algebraMap ℂ[X] (B F) a) =
      algebraMap Base (O F) (algebraMap ℂ[X] Base a) :=
    (IsScalarTower.algebraMap_apply ℂ[X] (B F) (O F) a).symm.trans
      (IsScalarTower.algebraMap_apply ℂ[X] Base (O F) a)
  change atDisk N p hRoots t w
      (e.symm (algebraMap (B F) (O F) (algebraMap ℂ[X] (B F) a))) = a.eval (j w)
  rw [hB,e.symm.commutes,AdjoinRoot.algebraMap_eq]
  exact polynomial_at_admissible N p hRoots t w hw a

private theorem chart_eval_no_pole
    (hN : 1 < N) (t : Period) (τ : UpperHalfPlane)
    (e : OrdinaryRoot N p ≃ₐ[Base] O F) (b : B F) :
    0 ≤ meromorphicOrderAt (fun w => puncturedChartEvaluation N p hRoots t e w b) (τ : ℂ) := by
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : FaithfulSMul (B F) F := IsIntegralClosure.faithfulSMul ℂ[X] (B F) F
  have hb : IsIntegral ℂ[X] b :=
    (isIntegral_algebraMap_iff (R := ℂ[X]) (A := B F) (B := F)).mp b.property
  obtain ⟨P,hP,hPb⟩ := hb
  let ψ := puncturedChartEvaluation N p hRoots t e
  have hmer : MeromorphicAt (fun w => ψ w b) (τ : ℂ) :=
    section_meromorphic N p hRoots t hN τ (e.symm (algebraMap (B F) (O F) b))
  apply nonnegative_from_monic_relation τ _ hmer P hP
  filter_upwards [eventually_ordinary_in_punctured_period τ] with w hw
  have H := congrArg (ψ w) hPb
  change (ψ w) (P.eval₂ (algebraMap ℂ[X] (B F)) b) = (ψ w) 0 at H
  rw [Polynomial.hom_eval₂, chart_polynomial_evaluation N p hRoots t e w hw, map_zero] at H
  exact H

private theorem center_character_of_limits
    {T : Type*} [CommRing T] (ψ : ℂ → T →+* ℂ) (c : ℂ)
    (H : ∀ b : T, ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧
      (fun w => ψ w b) =ᶠ[𝓝[≠] c] g) :
    ∃ χ : T →+* ℂ, ∀ b : T,
      Tendsto (fun w => ψ w b) (𝓝[≠] c) (𝓝 (χ b)) ∧
      AnalyticAt ℂ (Function.update (fun w => ψ w b) c (χ b)) c := by
  classical
  choose U hU hEq using H
  let v := fun b : T => U b c
  have hl (b : T) : Tendsto (fun w => ψ w b) (𝓝[≠] c) (𝓝 (v b)) :=
    (hU b).continuousAt.continuousWithinAt.tendsto.congr' (hEq b).symm
  let χ : T →+* ℂ := {
    toFun := v
    map_one' := tendsto_nhds_unique (hl 1) <| tendsto_const_nhds.congr'
      (Eventually.of_forall fun w => (map_one (ψ w)).symm)
    map_zero' := tendsto_nhds_unique (hl 0) <| tendsto_const_nhds.congr'
      (Eventually.of_forall fun w => (map_zero (ψ w)).symm)
    map_add' a b := tendsto_nhds_unique (hl (a+b)) <| ((hl a).add (hl b)).congr'
      (Eventually.of_forall fun w => (map_add (ψ w) a b).symm)
    map_mul' a b := tendsto_nhds_unique (hl (a*b)) <| ((hl a).mul (hl b)).congr'
      (Eventually.of_forall fun w => (map_mul (ψ w) a b).symm) }
  refine ⟨χ, fun b => ⟨hl b,?_⟩⟩
  apply (hU b).congr
  have he := eventually_nhdsWithin_iff.mp (hEq b)
  filter_upwards [he] with w hw
  by_cases hn : w = c
  · subst w
    change U b c = Function.update (fun z => ψ z b) c (U b c) c
    exact (Function.update_self _ _ _).symm
  · rw [Function.update_of_ne hn]
    exact (hw (Set.mem_compl_iff.mpr (fun h => hn (Set.mem_singleton_iff.mp h)))).symm

/-- The center of the marked finite-J analytic chart defines an actual
ring character of the very same compact finite-J normal order. It is
the unique limit of the original punctured evaluation on every
section, preserves the whole finite-J coefficient map, and all updated
section evaluations are holomorphic at the center. -/
theorem actual_marked_finiteJ_center
    (hN : 5 ≤ N) (τ : UpperHalfPlane)
    (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (hf : IsField (AdjoinRoot (P N p))) :
    letI : Field (K N p) := (whole_isField N p hf).toField
    let F := K N p
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    ∃ (t : Period) (α : O F →+* F) (e : OrdinaryRoot N p ≃ₐ[Base] O F)
      (χ : B F →+* ℂ),
      α.comp (algebraMap (B F) (O F)) = algebraMap (B F) F ∧
      (∀ r : OrdinaryRoot N p, α (e r) = literalWholeTensor N p (r ⊗ₜ[Base] (1 : Generic))) ∧
      χ.comp (algebraMap ℂ[X] (B F)) = Polynomial.evalRingHom (j (τ : ℂ)) ∧
      Function.Surjective χ ∧
      (∀ χ' : B F →+* ℂ,
        (∀ b : B F, Tendsto (fun w => puncturedChartEvaluation N p hRoots t e w b)
          (𝓝[≠] (τ : ℂ)) (𝓝 (χ' b))) → χ' = χ) ∧
      (∀ b : B F,
        0 ≤ meromorphicOrderAt (fun w => puncturedChartEvaluation N p hRoots t e w b) (τ : ℂ) ∧
        Tendsto (fun w => puncturedChartEvaluation N p hRoots t e w b) (𝓝[≠] (τ : ℂ))
          (𝓝 (χ b)) ∧
        AnalyticAt ℂ (Function.update (fun w => puncturedChartEvaluation N p hRoots t e w b)
          (τ : ℂ) (χ b)) (τ : ℂ)) := by
  letI : Field (K N p) := (whole_isField N p hf).toField
  let F := K N p
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  obtain ⟨α,e,hα,he⟩ := actual_literal_ordinary_normalization N p hp hd hf
  obtain ⟨t⟩ := exists_ordinary_seed
  let ψ := puncturedChartEvaluation N p hRoots t e
  have hN' : 1 < N := by omega
  have hNonneg (b : B F) : 0 ≤ meromorphicOrderAt (fun w => ψ w b) (τ : ℂ) :=
    chart_eval_no_pole N p hRoots hN' t τ e b
  have H (b : B F) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      (fun w => ψ w b) =ᶠ[𝓝[≠] (τ : ℂ)] g := by
    have hmer : MeromorphicAt (fun w => ψ w b) (τ : ℂ) :=
      section_meromorphic N p hRoots t hN' τ (e.symm (algebraMap (B F) (O F) b))
    exact hmer.meromorphicOrderAt_nonneg_iff.mp (hNonneg b)
  obtain ⟨χ,hχ⟩ := center_character_of_limits ψ (τ : ℂ) H
  have hχBase : χ.comp (algebraMap ℂ[X] (B F)) =
      Polynomial.evalRingHom (j (τ : ℂ)) := by
    apply RingHom.ext
    intro a
    have hw : (fun w => ψ w (algebraMap ℂ[X] (B F) a)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun w => a.eval (j w) := by
      filter_upwards [eventually_ordinary_in_punctured_period τ] with w hw
      exact RingHom.congr_fun (chart_polynomial_evaluation N p hRoots t e w hw) a
    have ht : Tendsto (fun w => a.eval (j w)) (𝓝[≠] (τ : ℂ)) (𝓝 (a.eval (j (τ : ℂ)))) :=
      (polynomial_analytic τ a).continuousAt.continuousWithinAt.tendsto
    exact tendsto_nhds_unique (hχ _).1 (ht.congr' hw.symm)
  refine ⟨t,α,e,χ,hα,he,hχBase,?_,?_,fun b => ⟨hNonneg b,hχ b⟩⟩
  · intro a
    refine ⟨algebraMap ℂ[X] (B F) (Polynomial.C a),?_⟩
    exact (RingHom.congr_fun hχBase (Polynomial.C a)).trans (Polynomial.eval_C)
  · intro χ' hχ'
    apply RingHom.ext
    intro b
    exact tendsto_nhds_unique (hχ' b) (hχ b).1

end SelectedActualMarkedEllipticCenterCharacter318

#print axioms SelectedActualMarkedEllipticCenterCharacter318.actual_marked_finiteJ_center
