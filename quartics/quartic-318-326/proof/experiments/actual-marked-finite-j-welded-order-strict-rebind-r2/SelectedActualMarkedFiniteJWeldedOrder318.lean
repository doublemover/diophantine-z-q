module

public import SelectedActualMarkedEllipticArbitraryFieldOrder318
import all SelectedActualMarkedEllipticArbitraryFieldOrder318
public import SelectedActualFiniteJCanonicalPunctureComparison318
public import Mathlib.Analysis.Meromorphic.Order
import all SelectedActualLocalHolomorphicGerms318
import all SelectedActualMarkedCompactSchemeStalk318
import all SelectedActualMarkedEllipticLocalHolomorphicGerm318
import all SelectedActualMarkedEllipticCenterCharacter318
import all SelectedActualMarkedEllipticFieldContinuation318
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Order.AddGroupWithTop

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Filter Polynomial
open scoped Polynomial Topology TensorProduct nonZeroDivisors
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedComplexGenericRatFunc318 SelectedActualComplexOrdinaryScalar318
open SelectedActualComplexGenericChartClosures318 SelectedActualComplexGenericCompactNormal318
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra)
open SelectedActualLiteralMarkedOrdinaryNormalization318 (B O)
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedEllipticCenterCharacter318
open SelectedActualMarkedEllipticFieldContinuation318
open SelectedActualMarkedCompactSchemeStalk318
  (finiteJ_chart_germ localized_factor_is_actual chartPrime point_mem affine_stalk_equiv nongeneric_of_order_prime)
open SelectedActualLocalHolomorphicGerms318 SelectedActualEllipticFixedGermCore318
open SelectedActualEllipticAnalyticRotation318
open SelectedActualMarkedEllipticLocalHolomorphicGerm318 (actual_punctured_section_ne_zero center_prime_ne_bot)
open SelectedActualMarkedEllipticUniformizerOrderOne318 (no_nontrivial_local_symmetry_of_original_sections)
open SelectedActualMarkedEllipticArbitraryFieldOrder318
  (whole_chart_fraction_ring representation_of_holomorphic_germ fraction_order_of_holomorphic_readout)
open SelectedActualFiniteJCanonicalPunctureComparison318
open OpenJLocalComparison318 (j)

namespace SelectedActualMarkedFiniteJWeldedOrder318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hRoots : fullRootSet N p)

private theorem welded_stalk_germ
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
        (∀ b : B F, intoWhole N p (e.symm (algebraMap (B F) (O F) b)) =
          algebraMap (B F) F b) ∧
        (∀ b : B F, Tendsto (fun w => ψ w b) (𝓝[≠] (τ : ℂ)) (𝓝 (χ b))) ∧
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
    nongeneric_of_order_prime U.2 E P₀ (MulEquiv.isDomain _ E.toMulEquiv)
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
    have hmem : IsLocalization.mk' L b s ∈ IsLocalRing.maximalIdeal L ↔ b ∈ P₀ :=
      IsLocalization.AtPrime.mk'_mem_maximal_iff L P₀ b s
    have hzero : χ b = χ s * 0 ↔ b ∈ P₀ := by
      rw [mul_zero] <;> rfl
    exact (h₁.trans hzero).trans hmem.symm
  have hβ (b : B F) : Φ (algebraMap (B F) L b) =
      germ (τ : ℂ) (fun w => updatedEval (τ : ℂ) ψ χ w b) (H b) :=
    (localGerm_section (τ : ℂ) ψ χ H L P₀.primeCompl hden b).trans
      (sectionGerm_apply (τ : ℂ) ψ χ H b)
  have hW := section_weld_of_original_tensor N p hf α e hα he
  have hlim (b : B F) : Tendsto (fun w => ψ w b) (𝓝[≠] (τ : ℂ)) (𝓝 (χ b)) :=
    (hμ b).2.1
  refine ⟨t,e,χ,hx,l,Φ,ε,H,hW,hlim,hDVR,hΦ,hε,hBase,hker,hl,hβ,fun a => ?_⟩
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

private theorem welded_uniformizer_order_one
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
        (Φ : L →+* Hol (τ : ℂ))
        (H : ∀ b : B F,
          AnalyticAt ℂ (fun w => updatedEval (τ : ℂ) ψ χ w b) (τ : ℂ)),
        (∀ b : B F, intoWhole N p (e.symm (algebraMap (B F) (O F) b)) =
          algebraMap (B F) F b) ∧
        (∀ b : B F, Tendsto (fun w => ψ w b) (𝓝[≠] (τ : ℂ)) (𝓝 (χ b))) ∧
        IsDiscreteValuationRing ((model F).presheaf.stalk x) ∧
        (∀ a : Γ(model F,U.1), l ((model F).presheaf.germ U.1 x hx a) =
          algebraMap (B F) L (chartRingEquiv F 1 a)) ∧
        (∀ b : B F, Φ (algebraMap (B F) L b) =
          germ (τ : ℂ) (fun w => updatedEval (τ : ℂ) ψ χ w b) (H b)) ∧
        ∀ (π : L) (hi : Irreducible π) (hπ : IsLocalRing.maximalIdeal L = Ideal.span ({π} : Set L))
          (f : ℂ → ℂ) (ha : AnalyticAt ℂ f (τ : ℂ)),
          Φ π = germ (τ : ℂ) f ha → analyticOrderAt f (τ : ℂ) = 1 := by
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
  obtain ⟨t,e,χ,hx,l,Φ,ε,H,hW,hlim,hDVR,hΦ,hε,hBase,hker,hl,hβ,hConst⟩ :=
    welded_stalk_germ N p hRoots hN τ hp hd hf
  refine ⟨t,e,χ,hx,l,Φ,H,hW,hlim,hDVR,hl,hβ,?_⟩
  intro π hi hπ f ha hfG
  let c : ℂ := τ
  let P₀ := RingHom.ker χ
  letI : P₀.IsPrime := RingHom.ker_isPrime χ
  let L := Localization.AtPrime P₀
  let ψ := puncturedChartEvaluation N p hRoots t e
  let scalar : ℂ →+* L :=
    (algebraMap (B F) L).comp ((algebraMap ℂ[X] (B F)).comp Polynomial.C)
  have hSc (z : ℂ) : Φ (scalar z) = germ c (fun _ => z) analyticAt_const := hConst z
  have hValue (a : L) : value c (Φ a) = ε a := RingHom.congr_fun hε a
  have hzero : f c = 0 := by
    have hπz : ε π = 0 := (hker π).mpr
      (hπ.symm ▸ Ideal.mem_span_singleton_self π)
    calc
      f c = value c (germ c f ha) := (value_germ c f ha).symm
      _ = value c (Φ π) := congrArg (value c) hfG.symm
      _ = 0 := (hValue π).trans hπz
  have hf0 : analyticOrderAt f c ≠ 0 := ha.analyticOrderAt_ne_zero.mpr hzero
  have hfinite : analyticOrderAt f c ≠ ⊤ := by
    intro ht
    apply hi.ne_zero
    apply hΦ
    rw [map_zero,hfG]
    have hzA : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) c := analyticAt_const
    have hzG : germ c (fun _ : ℂ => (0 : ℂ)) hzA = (0 : Hol c) := by
      apply Subtype.ext
      unfold germ
      change (↑(0 : ℂ → ℂ) : Germ (𝓝 c) ℂ) = 0
      exact Germ.coe_zero
    exact ((germ_eq_iff ha hzA).mpr (analyticOrderAt_eq_top.mp ht)).trans hzG
  have hn := Nat.cast_analyticOrderNatAt hfinite
  let n := analyticOrderNatAt f c
  have hOrd : analyticOrderAt f c = n := hn.symm
  by_contra hBad
  have hn' : 1 < n := by
    have h0 : n ≠ 0 := fun hz => hf0 (by rw [hOrd,hz,Nat.cast_zero])
    have h1 : n ≠ 1 := fun hz => hBad (by rw [hOrd,hz,Nat.cast_one])
    omega
  obtain ⟨σ,hσ,hσc,hFix,hne⟩ := analytic_rotation_of_order_gt_one ha hn' hOrd
  have hPi : pullback σ hσ hσc (Φ π) = Φ π := by
    rw [hfG,pullback_germ]
    exact (germ_eq_iff (compose_at_center hσ hσc ha) ha).mpr hFix
  have hAll := fixed_of_uniformizer scalar ε π hker hπ Φ hValue hSc σ hσ hσc hPi
  apply no_nontrivial_local_symmetry_of_original_sections N p hRoots t e hN τ σ
    (by simpa only [hσc] using hσ.continuousAt.tendsto) hne
  intro b
  let F_b := fun w => updatedEval c ψ χ w b
  have hbEq : pullback σ hσ hσc (germ c F_b (H b)) = germ c F_b (H b) := by
    exact (congrArg (pullback σ hσ hσc) (hβ b)).symm.trans
      ((hAll (algebraMap (B F) L b)).trans (hβ b))
  rw [pullback_germ] at hbEq
  have hg : (F_b ∘ σ) =ᶠ[𝓝 c] F_b :=
    (germ_eq_iff (compose_at_center hσ hσc (H b)) (H b)).mp hbEq
  filter_upwards [hg.filter_mono nhdsWithin_le_nhds,hne,self_mem_nhdsWithin]
    with w he hm hw
  have hw' : w ≠ c := fun h => hw (Set.mem_singleton_iff.mpr h)
  change F_b (σ w) = F_b w at he
  unfold F_b at he
  rw [updatedEval_away c ψ χ b hm.1,updatedEval_away c ψ χ b hw'] at he
  exact he

/-- The literal finite-J stalk and the original marked meromorphic readout, with the
same chosen normalization witness retained at every step. -/
theorem actual_whole_field_marked_finiteJ_order_with_weld
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
    letI : IsIntegral (model F) := model_integral F
    let U := sourceCover F 1
    ∃ (t : Period) (e : OrdinaryRoot N p ≃ₐ[Base] O F) (χ : B F →+* ℂ),
      let P₀ := RingHom.ker χ
      letI : P₀.IsPrime := RingHom.ker_isPrime χ
      let L := Localization.AtPrime P₀
      let x := U.2.fromSpec
        ((⟨P₀,inferInstance⟩ : PrimeSpectrum (B F)).comap (chartRingEquiv F 1).toRingHom)
      let R := (model F).presheaf.stalk x
      let ψ := puncturedChartEvaluation N p hRoots t e
      ∃ (l : R ≃+* L) (hDVR : IsDiscreteValuationRing R) (β : R →+* F),
        letI : IsDiscreteValuationRing R := hDVR
        let ι := fun a : B F => l.symm (algebraMap (B F) L a)
        (∀ b : B F, intoWhole N p (e.symm (algebraMap (B F) (O F) b)) =
          algebraMap (B F) F b) ∧
        (∀ b : B F, Tendsto (fun w => ψ w b) (𝓝[≠] (τ : ℂ)) (𝓝 (χ b))) ∧
        Spec.map (CommRingCat.ofHom β) ≫ (model F).fromSpecStalk x =
          (genericMap F).toNormalization ∧
        (∀ a : B F, β (ι a) = algebraMap (B F) F a) ∧
        ∀ (h : F), h ≠ 0 → ∃ a b : B F,
          let g := fun w : ℂ => ψ w a / ψ w b
          ι a ≠ 0 ∧ ι b ≠ 0 ∧ h = β (ι a) / β (ι b) ∧
          (∀ᶠ w in 𝓝[≠] (τ : ℂ), ψ w b ≠ 0) ∧
          MeromorphicAt g (τ : ℂ) ∧
          meromorphicOrderAt g (τ : ℂ) =
            (((IsDiscreteValuationRing.addVal R (ι a)).toNat : ℤ) -
              ((IsDiscreteValuationRing.addVal R (ι b)).toNat : ℤ) : WithTop ℤ) ∧
          ∃ (other : Period) (d : Base) (r : OrdinaryRoot N p),
            let s := AdjoinRoot.of (pC N p) d
            let g₀ := fun w : ℂ => atDisk N p hRoots other w r / atDisk N p hRoots other w s
            d ≠ 0 ∧ h * intoWhole N p s = intoWhole N p r ∧
            (∀ᶠ w in 𝓝[≠] (τ : ℂ),
              OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex w) ∧
              (HolomorphicCharts318.localChart N hN τ).symm w =
                GammaOneAtlas318.quotientMap N (UpperHalfPlane.ofComplex w) ∧
              atDisk N p hRoots other w s ≠ 0) ∧
            g =ᶠ[𝓝[≠] (τ : ℂ)] g₀ ∧ MeromorphicAt g₀ (τ : ℂ) ∧
            meromorphicOrderAt g₀ (τ : ℂ) =
              (((IsDiscreteValuationRing.addVal R (ι a)).toNat : ℤ) -
                ((IsDiscreteValuationRing.addVal R (ι b)).toNat : ℤ) : WithTop ℤ) := by
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
  letI : IsFractionRing (B F) F := whole_chart_fraction_ring N p hp hf
  let U := sourceCover F 1
  obtain ⟨t,e,χ,hx,l,Φ,H,hW,hlim,hDVR,hl,hΦβ,hOrd⟩ :=
    welded_uniformizer_order_one N p hRoots hN τ hp hd hf
  let P₀ := RingHom.ker χ
  letI : P₀.IsPrime := RingHom.ker_isPrime χ
  let L := Localization.AtPrime P₀
  let x := U.2.fromSpec
    ((⟨P₀,inferInstance⟩ : PrimeSpectrum (B F)).comap (chartRingEquiv F 1).toRingHom)
  let R := (model F).presheaf.stalk x
  letI : IsDiscreteValuationRing R := hDVR
  let φ : R →+* Hol (τ : ℂ) := Φ.comp l.toRingHom
  let ι := fun a : B F => l.symm (algebraMap (B F) L a)
  let ψ := puncturedChartEvaluation N p hRoots t e
  have hinj : Function.Injective (algebraMap (B F) F) := IsFractionRing.injective (B F) F
  have hDen (s : P₀.primeCompl) : IsUnit (algebraMap (B F) F s) := by
    have hn : χ s ≠ 0 := Ideal.mem_primeCompl_iff.mp s.property
    apply isUnit_iff_ne_zero.mpr
    intro h
    have hs : (s : B F) = 0 := hinj (h.trans (map_zero (algebraMap (B F) F)).symm)
    exact hn ((congrArg χ hs).trans (map_zero χ))
  let βL : L →+* F := IsLocalization.lift (M := P₀.primeCompl)
    (g := algebraMap (B F) F) hDen
  let β : R →+* F := βL.comp l.toRingHom
  have hβ (a : B F) : β (ι a) = algebraMap (B F) F a := by
    change βL (l (l.symm (algebraMap (B F) L a))) = _
    rw [l.apply_symm_apply]
    exact IsLocalization.lift_eq hDen a
  have hδ (a : Γ(model F,U.1)) :
      β ((model F).presheaf.germ U.1 x hx a) =
        algebraMap (B F) F (chartRingEquiv F 1 a) := by
    change βL (l ((model F).presheaf.germ U.1 x hx a)) = _
    rw [hl a]
    exact IsLocalization.lift_eq hDen _
  let ν := (genericMap F).toNormalization
  have hTop : (⊤ : (Spec (CommRingCat.of F)).Opens) ≤ ν ⁻¹ᵁ U.1 := by
    change ⊤ ≤ (genericMap F).toNormalization ⁻¹ᵁ
      ((genericMap F).fromNormalization ⁻¹ᵁ (JLineAtlas318.chart ℂ (1 : Fin 2) ''ᵁ ⊤))
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
    exact (NormalizationChart318.whole_preimage
      (CommRingCat.ofHom (polynomial F 1)) (JLineAtlas318.chart ℂ 1)).ge
  have hMorphism : Spec.map (CommRingCat.ofHom β) ≫ (model F).fromSpecStalk x = ν :=
    localized_factor_is_actual U.2 (chartRingEquiv F 1) ν x hx β hTop
      (finiteJ_chart_germ F) hδ
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  letI : IsDomain L := MulEquiv.isDomain R l.symm.toMulEquiv
  letI : IsDiscreteValuationRing L :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (A := R) (B := L) l
  have hπL : Irreducible (l π) := (MulEquiv.irreducible_iff (f := l.toMulEquiv)).mpr hπ
  have hspan : IsLocalRing.maximalIdeal L = Ideal.span ({l π} : Set L) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (R := L) (l π)).mp hπL
  obtain ⟨u,hu,huβ⟩ := representation_of_holomorphic_germ (φ π)
  have huOrd : analyticOrderAt u (τ : ℂ) = 1 := hOrd (l π) hπL hspan u hu huβ
  let read := fun a : B F => fun w => updatedEval (τ : ℂ) ψ χ w a
  have hRead (a : B F) : φ (ι a) = germ (τ : ℂ) (read a) (H a) := by
    change Φ (l (l.symm (algebraMap (B F) L a))) = _
    rw [l.apply_symm_apply]
    exact hΦβ a
  have hPert (a : B F) : read a =ᶠ[𝓝[≠] (τ : ℂ)] fun w => ψ w a := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact updatedEval_away (τ : ℂ) ψ χ a (fun h => hw (Set.mem_singleton_iff.mpr h))
  let ψfun : ℂ → B F → ℂ := fun w a => ψ w a
  have hFrac := fraction_order_of_holomorphic_readout
    (A := B F) (F := F) (R := R) (c := (τ : ℂ))
    φ ι β π hπ u hu huβ huOrd read ψfun H hRead hPert hβ
  refine ⟨t,e,χ,l,hDVR,β,hW,hlim,hMorphism,hβ,?_⟩
  intro h hh
  obtain ⟨a,b,ha,hb,hRatio,hDenG,hMerG,hOrder⟩ := hFrac h hh
  have hQuot : h = algebraMap (B F) F a / algebraMap (B F) F b := by
    simpa only [hβ] using hRatio
  obtain ⟨other,d,r,hd₀,hr,hDen₀,hMer₀⟩ :=
    whole_field_meromorphic_at_finite_branch N p hRoots hN τ h
  have hG := finiteJ_fraction_matches_original_puncture N p hRoots hp hf τ t other
    e hW a b h d r hDenG hQuot hd₀ hr
  refine ⟨a,b,ha,hb,hRatio,hDenG,hMerG,hOrder,other,d,r,hd₀,hr,hDen₀,hG,hMer₀,?_⟩
  exact (meromorphicOrderAt_congr hG).symm.trans hOrder

end SelectedActualMarkedFiniteJWeldedOrder318

#print axioms SelectedActualMarkedFiniteJWeldedOrder318.actual_whole_field_marked_finiteJ_order_with_weld
