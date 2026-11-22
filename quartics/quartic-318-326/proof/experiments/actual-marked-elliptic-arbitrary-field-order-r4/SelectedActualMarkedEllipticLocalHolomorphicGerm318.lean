module

public import SelectedActualLocalHolomorphicGerms318
import all SelectedActualLocalHolomorphicGerms318
public import SelectedActualMarkedEllipticSchemeBranch318
public import SelectedActualMarkedTensorOrdinaryIntoWhole318
import all SelectedActualMarkedEllipticFieldContinuation318
import all SelectedActualMarkedEllipticCenterCharacter318
import all SelectedActualMarkedCompactSchemeStalk318

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Filter Polynomial
open scoped Polynomial TensorProduct Topology
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexGenericChartClosures318
open SelectedActualComplexGenericCompactNormal318
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra literalWholeTensor)
open SelectedActualLiteralMarkedOrdinaryNormalization318 (B O)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedEllipticCenterCharacter318
open SelectedActualMarkedEllipticFieldContinuation318 (base_not_zero eventually_ordinary_in_punctured_period)
open SelectedActualMarkedTensorOrdinaryIntoWhole318 (literalWholeTensor_eq_intoWhole)
open SelectedActualMarkedCompactSchemeStalk318 (chartPrime point_mem affine_stalk_equiv nongeneric_of_order_prime)
open SelectedActualLocalHolomorphicGerms318
open OpenJLocalComparison318 (j)

namespace SelectedActualMarkedEllipticLocalHolomorphicGerm318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hRoots : fullRootSet N p)

/-- Injectivity on the analytic puncture uses the inverse in the very
same whole field. Clear its denominator over the original ordinary
base and reflect the product back into the original marked chart. -/
private theorem actual_punctured_section_ne_zero
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p)))
    (t : Period) (τ : UpperHalfPlane) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    ∀ (α : O F →+* F) (e : OrdinaryRoot N p ≃ₐ[Base] O F),
      α.comp (algebraMap (B F) (O F)) = algebraMap (B F) F →
      (∀ r : OrdinaryRoot N p, α (e r) =
        literalWholeTensor N p (r ⊗ₜ[Base] (1 : Generic))) →
      ∀ b : B F, b ≠ 0 → ∀ᶠ w in 𝓝[≠] (τ : ℂ),
        puncturedChartEvaluation N p hRoots t e w b ≠ 0 := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  intro α e hα he b hb
  let r : OrdinaryRoot N p := e.symm (algebraMap (B F) (O F) b)
  let z : F := intoWhole N p r
  have hz : z = algebraMap (B F) F b := by
    calc
      z = literalWholeTensor N p (r ⊗ₜ[Base] (1 : Generic)) :=
        (literalWholeTensor_eq_intoWhole N p r).symm
      _ = α (e r) := (he r).symm
      _ = α (algebraMap (B F) (O F) b) := congrArg α (e.apply_symm_apply _)
      _ = algebraMap (B F) F b := RingHom.congr_fun hα b
  have hzn : z ≠ 0 := by
    intro h
    apply hb
    apply Subtype.ext
    exact hz.symm.trans h
  obtain ⟨d,hd,s,hs⟩ := clear_in_whole N p z⁻¹
  let a : OrdinaryRoot N p := AdjoinRoot.of (pC N p) d
  have hprod : r*s = a := by
    apply intoWhole_injective N p hp
    rw [map_mul]
    change z * intoWhole N p s = intoWhole N p a
    have hs' : z⁻¹ * intoWhole N p a = intoWhole N p s := hs
    rw [← hs',← mul_assoc,mul_inv_cancel₀ hzn,one_mul]
  filter_upwards [base_not_zero N p hRoots t τ d hd] with w hw
  have hh := congrArg (atDisk N p hRoots t w) hprod
  rw [map_mul] at hh
  change atDisk N p hRoots t w r ≠ 0
  intro hr
  exact hw (hh.symm.trans (by rw [hr,zero_mul]))

private theorem center_prime_ne_bot
    (F : Type) [Field F] [Algebra JField F] (χ : B F →+* ℂ) (c : ℂ)
    (hχ : χ.comp (algebraMap ℂ[X] (B F)) = Polynomial.evalRingHom c) :
    RingHom.ker χ ≠ ⊥ := by
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  let a : ℂ[X] := Polynomial.X - Polynomial.C c
  let b : B F := algebraMap ℂ[X] (B F) a
  have hb : χ b = 0 :=
    (RingHom.congr_fun hχ a).trans (by
      change a.eval c = 0
      simp only [a,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_self])
  have hinj : Function.Injective (polynomial F 1) := by
    letI : Algebra ℂ[X] JField := (basePolynomial 1).toAlgebra
    letI : IsFractionRing ℂ[X] JField := base_fractionRing 1
    exact (algebraMap JField F).injective.comp (IsFractionRing.injective ℂ[X] JField)
  intro hQ
  have hzero : b = 0 := Ideal.mem_bot.mp (hQ ▸ (show b ∈ RingHom.ker χ from hb))
  have h := congrArg (algebraMap (B F) F) hzero
  change algebraMap (B F) F (algebraMap ℂ[X] (B F) a) = algebraMap (B F) F 0 at h
  rw [← IsScalarTower.algebraMap_apply ℂ[X] (B F) F,map_zero] at h
  exact Polynomial.X_sub_C_ne_zero c (hinj (h.trans (map_zero (polynomial F 1)).symm))

/-- The analytic ring of germs is attached to the same finite-J
normalization stalk, with centre value given by the same marked
character. The statement exposes the literal section beta, useful
for reading J and the numerator of the marked abscissa together. -/
theorem actual_marked_elliptic_stalk_holomorphic_germ
    (hN : 5 ≤ N) (τ : UpperHalfPlane) (hp : p.Monic)
    (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
    letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
    letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
    letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
      @IsScalarTower.of_algebraMap_eq' ℂ JField F
        inferInstance inferInstance inferInstance aF aJ aC (by rfl)
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    letI : Algebra Base F := ordinaryFieldAlgebra N p
    let U := sourceCover F 1
    ∃ (t : Period) (e : OrdinaryRoot N p ≃ₐ[Base] O F) (χ : B F →+* ℂ),
      let P₀ := RingHom.ker χ
      letI : P₀.IsPrime := RingHom.ker_isPrime χ
      let L := Localization.AtPrime P₀
      let x := U.2.fromSpec
        ((⟨P₀,inferInstance⟩ : PrimeSpectrum (B F)).comap (chartRingEquiv F 1).toRingHom)
      let ψ := puncturedChartEvaluation N p hRoots t e
      ∃ (hx : x ∈ U.1) (l : ((model F).presheaf.stalk x) ≃+* L)
        (Φ : L →+* Hol (τ : ℂ)) (ε : L →+* ℂ)
        (H : ∀ b : B F,
          AnalyticAt ℂ (fun w => updatedEval (τ : ℂ) ψ χ w b) (τ : ℂ)),
        IsDiscreteValuationRing ((model F).presheaf.stalk x) ∧
        Function.Injective Φ ∧
        (value (τ : ℂ)).comp Φ = ε ∧
        χ.comp (algebraMap ℂ[X] (B F)) = Polynomial.evalRingHom (j (τ : ℂ)) ∧
        (∀ z : L, ε z = 0 ↔ z ∈ IsLocalRing.maximalIdeal L) ∧
        (∀ a : Γ(model F,U.1), l ((model F).presheaf.germ U.1 x hx a) =
          algebraMap (B F) L (chartRingEquiv F 1 a)) ∧
        (∀ b : B F, Φ (algebraMap (B F) L b) =
          germ (τ : ℂ) (fun w => updatedEval (τ : ℂ) ψ χ w b) (H b)) ∧
        (∀ a : ℂ, Φ (algebraMap (B F) L (algebraMap ℂ[X] (B F) (Polynomial.C a))) =
          germ (τ : ℂ) (fun _ => a) analyticAt_const) := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
  letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
  letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
  letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℂ JField F
      inferInstance inferInstance inferInstance aF aJ aC (by rfl)
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : Algebra Base F := ordinaryFieldAlgebra N p
  letI : IsIntegral (model F) := model_integral F
  let U := sourceCover F 1
  obtain ⟨t,α,e,χ,hα,he,hBase,hSurj,hUnique,hμ⟩ :=
    actual_marked_finiteJ_center N p hRoots hN τ hp hd hf
  let P₀ := RingHom.ker χ
  letI : P₀.IsPrime := RingHom.ker_isPrime χ
  let L := Localization.AtPrime P₀
  let E : Γ(model F,U.1) ≃+* B F := chartRingEquiv F 1
  let x := U.2.fromSpec (chartPrime E P₀)
  let hx : x ∈ U.1 := point_mem U.2 E P₀
  obtain ⟨l,hl⟩ := affine_stalk_equiv U.2 E P₀
  have hxng : x ≠ genericPoint (model F) :=
    nongeneric_of_order_prime U.2 E P₀ (chart_domain_normal F 1).1
      (center_prime_ne_bot F χ (j (τ : ℂ)) hBase)
  have hDVR : IsDiscreteValuationRing ((model F).presheaf.stalk x) :=
    (literal_projective_normalization N p hp hf).2 x hxng
  let ψ := puncturedChartEvaluation N p hRoots t e
  have H (b : B F) : AnalyticAt ℂ (fun w => updatedEval (τ : ℂ) ψ χ w b) (τ : ℂ) := by
    rw [updatedEval_eq_update]
    exact (hμ b).2.2
  have hden (s : P₀.primeCompl) : χ s ≠ 0 :=
    Ideal.mem_primeCompl_iff.mp s.property
  let Φ : L →+* Hol (τ : ℂ) := localGerm (τ : ℂ) ψ χ H L P₀.primeCompl hden
  let ε : L →+* ℂ := localCenter χ L P₀.primeCompl hden
  have hΦ : Function.Injective Φ :=
    injective_localGerm (τ : ℂ) ψ χ H L P₀.primeCompl hden
      (actual_punctured_section_ne_zero N p hRoots hp hf t τ α e hα he)
  have hε : (value (τ : ℂ)).comp Φ = ε :=
    value_localGerm (τ : ℂ) ψ χ H L P₀.primeCompl hden
  have hker (z : L) : ε z = 0 ↔ z ∈ IsLocalRing.maximalIdeal L := by
    obtain ⟨b,s,rfl⟩ := IsLocalization.exists_mk'_eq P₀.primeCompl z
    have h₁ : ε (IsLocalization.mk' L b s) = 0 ↔ χ b = χ s * 0 := by
      unfold ε localCenter
      exact IsLocalization.lift_mk'_spec _ b 0 s
    rw [h₁,mul_zero,IsLocalization.AtPrime.mk'_mem_maximal_iff] <;> rfl
  have hβ (b : B F) : Φ (algebraMap (B F) L b) =
      germ (τ : ℂ) (fun w => updatedEval (τ : ℂ) ψ χ w b) (H b) :=
    (localGerm_section (τ : ℂ) ψ χ H L P₀.primeCompl hden b).trans
      (sectionGerm_apply (τ : ℂ) ψ χ H b)
  refine ⟨t,e,χ,hx,l,Φ,ε,H,hDVR,hΦ,hε,hBase,hker,hl,hβ,fun a => ?_⟩
  let b : B F := algebraMap ℂ[X] (B F) (Polynomial.C a)
  change Φ (algebraMap (B F) L b) = germ (τ : ℂ) (fun _ => a) analyticAt_const
  rw [hβ]
  apply (germ_eq_iff (H b) analyticAt_const).mpr
  have hpunct : ∀ᶠ w in 𝓝[≠] (τ : ℂ), ψ w b = a := by
    filter_upwards [eventually_ordinary_in_punctured_period τ] with w hw
    exact (RingHom.congr_fun (chart_polynomial_evaluation N p hRoots t e w hw)
      (Polynomial.C a)).trans Polynomial.eval_C
  have hc : χ b = a :=
    (RingHom.congr_fun hBase (Polynomial.C a)).trans Polynomial.eval_C
  filter_upwards [eventually_nhdsWithin_iff.mp hpunct] with w hw
  by_cases heq : w = (τ : ℂ)
  · subst w
    exact (updatedEval_center (τ : ℂ) ψ χ b).trans hc
  · exact (updatedEval_away (τ : ℂ) ψ χ b heq).trans
      (hw (fun h => heq (Set.mem_singleton_iff.mp h)))

end SelectedActualMarkedEllipticLocalHolomorphicGerm318

#print axioms SelectedActualMarkedEllipticLocalHolomorphicGerm318.actual_marked_elliptic_stalk_holomorphic_germ
