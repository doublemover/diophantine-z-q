module

public import SelectedActualMarkedEllipticCenterCharacter318
import all SelectedActualMarkedEllipticCenterCharacter318
public import SelectedActualMarkedTensorOrdinaryIntoWhole318
import all SelectedActualMarkedEllipticFieldContinuation318
import all SelectedActualWholeMarkedOrdinaryMeromorphicGerm318

public section
noncomputable section

open Filter Polynomial
open scoped Polynomial Topology TensorProduct
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexGenericChartClosures318
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra literalWholeTensor)
open SelectedActualLiteralMarkedOrdinaryNormalization318 (B O actual_literal_ordinary_normalization)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedEllipticCenterCharacter318
open SelectedActualMarkedEllipticFieldContinuation318
open SelectedActualMarkedTensorOrdinaryIntoWhole318 (literalWholeTensor_eq_intoWhole)

namespace SelectedActualFiniteJCanonicalPunctureComparison318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hRoots : fullRootSet N p)

/-- Read a section of the actual finite chart through its actual ordinary
normalization isomorphism and the installed whole field. This is the
same map supplied by its literal tensor diagram, not a fresh map. -/
theorem section_weld_of_original_tensor (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    ∀ (α : O F →+* F) (e : OrdinaryRoot N p ≃ₐ[Base] O F),
      α.comp (algebraMap (B F) (O F)) = algebraMap (B F) F →
      (∀ r : OrdinaryRoot N p, α (e r) = literalWholeTensor N p (r ⊗ₜ[Base] (1 : Generic))) →
      ∀ b : B F, intoWhole N p (e.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  change ∀ (α : O F →+* F) (e : OrdinaryRoot N p ≃ₐ[Base] O F),
    α.comp (algebraMap (B F) (O F)) = algebraMap (B F) F →
    (∀ r : OrdinaryRoot N p, α (e r) = literalWholeTensor N p (r ⊗ₜ[Base] (1 : Generic))) →
    ∀ b : B F, intoWhole N p (e.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b
  intro α e hα he b
  let r : OrdinaryRoot N p := e.symm (algebraMap (B F) (O F) b)
  calc
    intoWhole N p r = literalWholeTensor N p (r ⊗ₜ[Base] (1 : Generic)) :=
      (literalWholeTensor_eq_intoWhole N p r).symm
    _ = α (e r) := (he r).symm
    _ = α (algebraMap (B F) (O F) b) := congrArg α (e.apply_symm_apply _)
    _ = algebraMap (B F) F b := RingHom.congr_fun hα b

/-- The original marked finite normalization constructs a witness with
the section weld. An arbitrary algebra isomorphism would not suffice. -/
theorem actual_finiteJ_chart_exists_with_section_weld
    (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    ∃ e : OrdinaryRoot N p ≃ₐ[Base] O F,
      ∀ b : B F, intoWhole N p (e.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  obtain ⟨α,e,hα,he⟩ := actual_literal_ordinary_normalization N p hp hd hf
  exact ⟨e, section_weld_of_original_tensor N p hf α e hα he⟩

/-- At a genuinely admissible archimedean point, the finite chart
center character is its specified ordinary character on the actual
integral order. The fallback period of the punctured evaluator does
not affect the character or its kernel. -/
theorem center_character_at_ordinary_period {F : Type} [Field F] [Algebra JField F]
    (hN : 1 < N) (t seed : Period) (e : OrdinaryRoot N p ≃ₐ[Base] O F)
    (χ : B F →+* ℂ)
    (hχ : ∀ b : B F,
      Tendsto (fun w => puncturedChartEvaluation N p hRoots seed e w b)
        (𝓝[≠] (t.val : ℂ)) (𝓝 (χ b))) :
    χ = (atPeriod N p hRoots t).comp (e.symm.toRingHom.comp (algebraMap (B F) (O F))) := by
  apply RingHom.ext
  intro b
  let r : OrdinaryRoot N p := e.symm (algebraMap (B F) (O F) b)
  have hlim : Tendsto (fun w => atDisk N p hRoots t w r)
      (𝓝[≠] (t.val : ℂ)) (𝓝 (atDisk N p hRoots t (t.val : ℂ) r)) :=
    (ordinary_ring_analytic N p hN hRoots t r).continuousAt.continuousWithinAt.tendsto
  have hdisk : atDisk N p hRoots t (t.val : ℂ) r = atPeriod N p hRoots t r := by
    have h : UpperHalfPlane.ofComplex (t.val : ℂ) = t.val := UpperHalfPlane.ofComplex_apply t.val
    have ht : OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex (t.val : ℂ)) :=
      h.symm ▸ t.property
    let t' : Period := ⟨UpperHalfPlane.ofComplex (t.val : ℂ),ht⟩
    have hT : t' = t := Subtype.ext h
    have heq : atDisk N p hRoots t (t.val : ℂ) = atPeriod N p hRoots t' :=
      atDisk_of_admissible N p hRoots t (t.val : ℂ) ht
    exact (congrArg (fun f : OrdinaryRoot N p →+* ℂ => f r) heq).trans
      (congrArg (fun v : Period => atPeriod N p hRoots v r) hT)
  have hEq : (fun w => atDisk N p hRoots t w r) =ᶠ[𝓝[≠] (t.val : ℂ)]
      fun w => puncturedChartEvaluation N p hRoots seed e w b := by
    filter_upwards [eventually_ordinary_in_punctured_period t.val] with w hw
    have heq : atDisk N p hRoots t w = atDisk N p hRoots seed w := by
      rw [atDisk_of_admissible N p hRoots t w hw,atDisk_of_admissible N p hRoots seed w hw]
    change atDisk N p hRoots t w r = atDisk N p hRoots seed w r
    exact congrArg (fun f : OrdinaryRoot N p →+* ℂ => f r) heq
  have hlim' : Tendsto (fun w => puncturedChartEvaluation N p hRoots seed e w b)
      (𝓝[≠] (t.val : ℂ)) (𝓝 (atPeriod N p hRoots t r)) := by
    rw [← hdisk]
    exact hlim.congr' hEq
  exact tendsto_nhds_unique (hχ b) hlim'

/-- Two lawful witnesses have the same ordinary character. The
pullback sections agree because both map to the same integral element
of the original field. There is no assumed equality of chart maps. -/
theorem ordinary_character_independent_of_chart_witness
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p))) (t : Period) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    ∀ (e₁ e₂ : OrdinaryRoot N p ≃ₐ[Base] O F),
      (∀ b : B F, intoWhole N p (e₁.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b) →
      (∀ b : B F, intoWhole N p (e₂.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b) →
      (atPeriod N p hRoots t).comp (e₁.symm.toRingHom.comp (algebraMap (B F) (O F))) =
        (atPeriod N p hRoots t).comp (e₂.symm.toRingHom.comp (algebraMap (B F) (O F))) := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  change ∀ (e₁ e₂ : OrdinaryRoot N p ≃ₐ[Base] O F),
    (∀ b : B F, intoWhole N p (e₁.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b) →
    (∀ b : B F, intoWhole N p (e₂.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b) →
    (atPeriod N p hRoots t).comp (e₁.symm.toRingHom.comp (algebraMap (B F) (O F))) =
      (atPeriod N p hRoots t).comp (e₂.symm.toRingHom.comp (algebraMap (B F) (O F)))
  intro e₁ e₂ h₁ h₂
  apply RingHom.ext
  intro b
  have h : e₁.symm (algebraMap (B F) (O F) b) = e₂.symm (algebraMap (B F) (O F) b) :=
    (intoWhole_injective N p hp) ((h₁ b).trans (h₂ b).symm)
  exact congrArg (fun a : OrdinaryRoot N p => atPeriod N p hRoots t a) h

/-- Match the finite normal chart fraction with the literal series
obtained by clearing the original whole field over its marked
ordinary chart. The same field identities imply the cross product
before any punctured evaluation. This works for all finite centers,
including the omitted elliptic ones. -/
theorem finiteJ_fraction_matches_original_puncture
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p)))
    (τ : UpperHalfPlane) (seed other : Period) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    ∀ (e : OrdinaryRoot N p ≃ₐ[Base] O F),
      (∀ b : B F, intoWhole N p (e.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b) →
      ∀ (a b : B F) (h : F) (d : Base) (r : OrdinaryRoot N p),
        (∀ᶠ w in 𝓝[≠] (τ : ℂ), puncturedChartEvaluation N p hRoots seed e w b ≠ 0) →
        h = algebraMap (B F) F a / algebraMap (B F) F b →
        d ≠ 0 → h * intoWhole N p (AdjoinRoot.of (pC N p) d) = intoWhole N p r →
        (fun w => puncturedChartEvaluation N p hRoots seed e w a /
          puncturedChartEvaluation N p hRoots seed e w b) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun w => atDisk N p hRoots other w r /
          atDisk N p hRoots other w (AdjoinRoot.of (pC N p) d) := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  change ∀ (e : OrdinaryRoot N p ≃ₐ[Base] O F),
    (∀ b : B F, intoWhole N p (e.symm (algebraMap (B F) (O F) b)) = algebraMap (B F) F b) →
    ∀ (a b : B F) (h : F) (d : Base) (r : OrdinaryRoot N p),
      (∀ᶠ w in 𝓝[≠] (τ : ℂ), puncturedChartEvaluation N p hRoots seed e w b ≠ 0) →
      h = algebraMap (B F) F a / algebraMap (B F) F b →
      d ≠ 0 → h * intoWhole N p (AdjoinRoot.of (pC N p) d) = intoWhole N p r →
      (fun w => puncturedChartEvaluation N p hRoots seed e w a /
        puncturedChartEvaluation N p hRoots seed e w b) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun w => atDisk N p hRoots other w r /
        atDisk N p hRoots other w (AdjoinRoot.of (pC N p) d)
  intro e hW a b h d r hb hq hd hr
  let A : OrdinaryRoot N p := e.symm (algebraMap (B F) (O F) a)
  let D : OrdinaryRoot N p := e.symm (algebraMap (B F) (O F) b)
  let s : OrdinaryRoot N p := AdjoinRoot.of (pC N p) d
  have hbn : b ≠ 0 := by
    intro h0
    obtain ⟨w,hw⟩ := hb.exists
    apply hw
    rw [h0,map_zero]
  have hbF : algebraMap (B F) F b ≠ 0 := by
    intro h0
    apply hbn
    apply (IsIntegralClosure.algebraMap_injective (B F) ℂ[X] F)
    exact h0.trans (map_zero (algebraMap (B F) F)).symm
  have hEq : A * s = r * D := by
    apply intoWhole_injective N p hp
    rw [map_mul,map_mul]
    change intoWhole N p A * intoWhole N p s = intoWhole N p r * intoWhole N p D
    have hA : intoWhole N p A = algebraMap (B F) F a := hW a
    have hD : intoWhole N p D = algebraMap (B F) F b := hW b
    rw [hA,hD]
    have hqs := (div_eq_iff hbF).mp hq
    calc
      algebraMap (B F) F a * intoWhole N p s =
          (h * algebraMap (B F) F b) * intoWhole N p s := congrArg (· * intoWhole N p s) hqs.symm
      _ = (h * intoWhole N p s) * algebraMap (B F) F b := by ac_rfl
      _ = intoWhole N p r * algebraMap (B F) F b :=
        congrArg (· * algebraMap (B F) F b) hr
  filter_upwards [hb,base_not_zero N p hRoots other τ d hd,
    eventually_ordinary_in_punctured_period τ] with w hbw hdw hw
  have hEval : atDisk N p hRoots other w = atDisk N p hRoots seed w := by
    rw [atDisk_of_admissible N p hRoots other w hw,atDisk_of_admissible N p hRoots seed w hw]
  have hdb : atDisk N p hRoots seed w D ≠ 0 := hbw
  have hds : atDisk N p hRoots seed w s ≠ 0 := by
    have hz : atDisk N p hRoots other w s ≠ 0 := hdw
    rwa [hEval] at hz
  change atDisk N p hRoots seed w A / atDisk N p hRoots seed w D =
    atDisk N p hRoots other w r / atDisk N p hRoots other w s
  rw [hEval]
  apply (div_eq_div_iff hdb hds).mpr
  simpa only [map_mul] using congrArg (atDisk N p hRoots seed w) hEq

end SelectedActualFiniteJCanonicalPunctureComparison318

#print axioms SelectedActualFiniteJCanonicalPunctureComparison318.section_weld_of_original_tensor
#print axioms SelectedActualFiniteJCanonicalPunctureComparison318.center_character_at_ordinary_period
#print axioms SelectedActualFiniteJCanonicalPunctureComparison318.finiteJ_fraction_matches_original_puncture
#print axioms SelectedActualFiniteJCanonicalPunctureComparison318.ordinary_character_independent_of_chart_witness
