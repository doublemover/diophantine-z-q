module

public import SelectedActualMarkedEllipticUniformizerOrderOne318
public import Mathlib.Analysis.Meromorphic.Order
import all SelectedActualLocalHolomorphicGerms318
import all SelectedActualMarkedCompactSchemeStalk318
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Order.Sub.WithTop

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Filter Polynomial
open scoped Polynomial Topology nonZeroDivisors
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedComplexGenericRatFunc318 SelectedActualComplexOrdinaryScalar318
open SelectedActualComplexGenericChartClosures318 SelectedActualComplexGenericCompactNormal318
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra)
open SelectedActualLiteralMarkedOrdinaryNormalization318 (B O)
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedEllipticCenterCharacter318
open SelectedActualMarkedCompactSchemeStalk318 (finiteJ_chart_germ localized_factor_is_actual)
open SelectedActualLocalHolomorphicGerms318
open SelectedActualMarkedEllipticUniformizerOrderOne318

namespace SelectedActualMarkedEllipticArbitraryFieldOrder318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private theorem representation_of_holomorphic_germ {c : ℂ} (v : Hol c) :
    ∃ f : ℂ → ℂ, ∃ hf : AnalyticAt ℂ f c, v = germ c f hf := by
  obtain ⟨f,hf,he⟩ := v.property
  exact ⟨f,hf,Subtype.ext he.symm⟩

private theorem unit_order {c : ℂ} {f : ℂ → ℂ} (hf : AnalyticAt ℂ f c) (h₀ : f c ≠ 0) :
    meromorphicOrderAt f c = 0 := by
  rw [hf.meromorphicOrderAt_eq,hf.analyticOrderAt_eq_zero.mpr h₀] <;> rfl

/-- Factor in the actual DVR first. The holomorphic readout of the
unit maps by the genuine center evaluation to a nonzero complex
number, so it contributes no order. -/
private theorem order_of_DVR_element
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {c : ℂ} (f : R →+* Hol c)
    (π : R) (hπ : Irreducible π)
    (u : ℂ → ℂ) (hu : AnalyticAt ℂ u c) (hfu : f π = germ c u hu)
    (ho : analyticOrderAt u c = 1)
    (a : R) (ha : a ≠ 0)
    (v : ℂ → ℂ) (hv : AnalyticAt ℂ v c) (hfv : f a = germ c v hv) :
    meromorphicOrderAt v c =
      (((IsDiscreteValuationRing.addVal R a).toNat : ℤ) : WithTop ℤ) := by
  obtain ⟨n,b,hb⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  obtain ⟨w,hw,hfw⟩ := representation_of_holomorphic_germ (f (b : R))
  have hw₀ : w c ≠ 0 := by
    have h := (b.isUnit.map ((value c).comp f)).ne_zero
    change value c (f (b : R)) ≠ 0 at h
    rwa [hfw,value_germ] at h
  have hwu : AnalyticAt ℂ (w * u^n) c := hw.mul (hu.pow n)
  have hprod : germ c w hw * (germ c u hu)^n = germ c (w * u^n) hwu := by
    apply Subtype.ext
    change Germ.ofFun w * (Germ.ofFun u)^n = Germ.ofFun (w * u^n)
    let g : (ℂ → ℂ) →+* Germ (𝓝 c) ℂ := Germ.coeRingHom (𝓝 c)
    exact ((map_mul g w (u^n)).trans (congrArg (g w * ·) (map_pow g u n))).symm
  have hvEq : germ c v hv = germ c (w * u^n) hwu := by
    calc
      germ c v hv = f a := hfv.symm
      _ = f (b : R) * (f π)^n := by rw [hb,map_mul,map_pow]
      _ = germ c (w * u^n) hwu := by rw [hfw,hfu,hprod]
  have he := (germ_eq_iff hv hwu).mp hvEq
  have hu₁ : meromorphicOrderAt u c = 1 := by
    rw [hu.meromorphicOrderAt_eq,ho] <;> rfl
  have hVal := IsDiscreteValuationRing.addVal_def a b hπ n hb
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_mul hw.meromorphicAt (hu.meromorphicAt.pow n),
    meromorphicOrderAt_pow hu.meromorphicAt,hu₁,unit_order hw hw₀,zero_add,mul_one,
    hVal,ENat.toNat_natCast,WithTop.coe_natCast]

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hRoots : fullRootSet N p)

private theorem whole_chart_fraction_ring
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
    IsFractionRing (B F) F := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra ℂ[X] JField := (basePolynomial 1).toAlgebra
  letI : IsFractionRing ℂ[X] JField := base_fractionRing 1
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  letI : IsScalarTower ℂ[X] JField F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hpC : (p.map (toComplex N)).Monic := hp.map (toComplex N)
  have hpG : (P N p).Monic := hpC.map (algebraMap Base Generic)
  have hpJ : (pJ N p).Monic := by
    unfold pJ
    letI : Algebra Base (RatFunc ℂ) := ratscalar
    exact hpG.map ratEquiv.toRingEquiv.toRingHom
  letI : FiniteDimensional JField F := hpJ.finite_adjoinRoot
  exact IsIntegralClosure.isFractionRing_of_finite_extension ℂ[X] JField F (B F)

/-- Readout of a field quotient is independent of the fraction.
The multiplication identity is reflected into the literal integral
order before applying the same original puncture character. -/
theorem actual_chart_fraction_germ_unique
    {F : Type} [Field F] [Algebra JField F]
    (t : Period) (e : OrdinaryRoot N p ≃ₐ[Base] O F)
    (τ : UpperHalfPlane) (a b a' b' : B F)
    (hinj : Function.Injective (algebraMap (B F) F))
    (hb : algebraMap (B F) F b ≠ 0) (hb' : algebraMap (B F) F b' ≠ 0)
    (h : algebraMap (B F) F a / algebraMap (B F) F b =
      algebraMap (B F) F a' / algebraMap (B F) F b')
    (h₁ : ∀ᶠ w in 𝓝[≠] (τ : ℂ), puncturedChartEvaluation N p hRoots t e w b ≠ 0)
    (h₂ : ∀ᶠ w in 𝓝[≠] (τ : ℂ), puncturedChartEvaluation N p hRoots t e w b' ≠ 0) :
    (fun w => puncturedChartEvaluation N p hRoots t e w a /
      puncturedChartEvaluation N p hRoots t e w b) =ᶠ[𝓝[≠] (τ : ℂ)]
    (fun w => puncturedChartEvaluation N p hRoots t e w a' /
      puncturedChartEvaluation N p hRoots t e w b') := by
  have hc : a * b' = a' * b := hinj (by
    rw [map_mul,map_mul]
    exact (div_eq_div_iff hb hb').mp h)
  filter_upwards [h₁,h₂] with w hw hw'
  apply (div_eq_div_iff hw hw').mpr
  simpa only [map_mul] using congrArg (puncturedChartEvaluation N p hRoots t e w) hc

/-- At the original marked compact finite-J point, a nonzero arbitrary
element of the same whole field has a punctured meromorphic readout
whose order is the stock normalized DVR order of that actual stalk.
Both generic factors and the chart section map are the original maps. -/
theorem actual_whole_field_marked_finiteJ_order
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
  obtain ⟨t,e,χ,hx,l,Φ,H,hDVR,hl,hΦβ,hOrd⟩ :=
    actual_marked_elliptic_uniformizer_order_one N p hRoots hN τ hp hd hf
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
  letI : IsDomain L := MulEquiv.isDomain L l.toMulEquiv
  letI : IsDiscreteValuationRing L := RingEquivClass.isDiscreteValuationRing l
  have hπL : Irreducible (l π) := (MulEquiv.irreducible_iff (f := l.toMulEquiv)).mpr hπ
  have hspan : IsLocalRing.maximalIdeal L = Ideal.span ({l π} : Set L) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπL
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
  have hNe (a : B F) (hah : algebraMap (B F) F a ≠ 0) : ι a ≠ 0 := by
    intro hh
    apply hah
    exact (hβ a).symm.trans ((congrArg β hh).trans (map_zero β))
  refine ⟨t,e,χ,l,hDVR,β,hMorphism,hβ,?_⟩
  intro h hh
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective (B F) h
  have hbF : algebraMap (B F) F b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have haF : algebraMap (B F) F a ≠ 0 := by
    intro hz
    apply hh
    rw [hz,zero_div] at hab
    exact hab.symm
  have haR := hNe a haF
  have hbR := hNe b hbF
  have haOrder := order_of_DVR_element φ π hπ u hu huβ huOrd (ι a) haR (read a) (H a) (hRead a)
  have hbOrder := order_of_DVR_element φ π hπ u hu huβ huOrd (ι b) hbR (read b) (H b) (hRead b)
  have hbEv : ∀ᶠ w in 𝓝[≠] (τ : ℂ), ψ w b ≠ 0 := by
    have hbFinite : meromorphicOrderAt (read b) (τ : ℂ) ≠ ⊤ := by
      rw [hbOrder]
      exact WithTop.coe_ne_top
    have hbn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (H b).meromorphicAt).mp hbFinite
    exact (hbn.and (hPert b)).mono fun w hw => hw.2 ▸ hw.1
  have hg : (read a / read b) =ᶠ[𝓝[≠] (τ : ℂ)] (fun w => ψ w a / ψ w b) := by
    filter_upwards [hPert a,hPert b] with w hwa hwb
    exact congrArg₂ (· / ·) hwa hwb
  refine ⟨a,b,haR,hbR,?_,hbEv,((H a).meromorphicAt.div (H b).meromorphicAt).congr hg.symm,?_⟩
  · rw [hβ a,hβ b]
    exact hab.symm
  · rw [← meromorphicOrderAt_congr hg,
      meromorphicOrderAt_div (H a).meromorphicAt (H b).meromorphicAt,haOrder,hbOrder] <;>
      exact (WithTop.LinearOrderedAddCommGroup.coe_sub _ _).symm

end SelectedActualMarkedEllipticArbitraryFieldOrder318

#print axioms SelectedActualMarkedEllipticArbitraryFieldOrder318.actual_whole_field_marked_finiteJ_order

#print axioms SelectedActualMarkedEllipticArbitraryFieldOrder318.actual_chart_fraction_germ_unique
