module

public import SelectedActualMarkedCuspSchemeStalkHolomorphicV2_318
public import SelectedActualMarkedCuspPunctureSeparation318
public import SelectedActualEllipticFixedGermCore318
public import SelectedActualEllipticAnalyticRotation318
import all SelectedActualMarkedCuspCenterCharacter318
import Mathlib.RingTheory.Localization.Integral

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Filter Polynomial Set
open scoped Polynomial Topology nonZeroDivisors
open FiniteCuspEnds318
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexOrdinaryScalar318
open SelectedActualComplexGenericChartClosures318 SelectedActualComplexGenericCompactNormal318
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedCuspPunctureEvaluation318
open SelectedActualMarkedCuspWholeField318 (Germ0)
open SelectedActualMarkedCuspCenterCharacter318
open SelectedActualCuspCanonicalChartReadout318
open SelectedActualMarkedCuspSchemeStalkHolomorphicV2_318
open SelectedActualMarkedCuspPunctureSeparation318
open SelectedActualLocalHolomorphicGerms318
open SelectedActualEllipticFixedGermCore318
open SelectedActualEllipticAnalyticRotation318

namespace SelectedActualMarkedCuspUniformizerOrderOneV2_318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private abbrev Punct := 𝓝[≠] (0 : ℂ)

private def pullPunct (σ : ℂ → ℂ) (hσ : Tendsto σ Punct Punct) : Germ0 →+* Germ0 where
  toFun u := u.compTendsto σ hσ
  map_zero' := Germ.coe_compTendsto (fun _ => (0 : ℂ)) hσ
  map_one' := Germ.coe_compTendsto (fun _ => (1 : ℂ)) hσ
  map_add' u v := by
    refine Germ.inductionOn₂ u v (fun f g => ?_)
    change (Germ.ofFun (f+g)).compTendsto σ hσ =
      (Germ.ofFun f).compTendsto σ hσ + (Germ.ofFun g).compTendsto σ hσ
    rw [Germ.coe_compTendsto (f+g) hσ,Germ.coe_compTendsto f hσ,Germ.coe_compTendsto g hσ]
    exact Germ.coe_add (f ∘ σ) (g ∘ σ)
  map_mul' u v := by
    refine Germ.inductionOn₂ u v (fun f g => ?_)
    change (Germ.ofFun (f*g)).compTendsto σ hσ =
      (Germ.ofFun f).compTendsto σ hσ * (Germ.ofFun g).compTendsto σ hσ
    rw [Germ.coe_compTendsto (f*g) hσ,Germ.coe_compTendsto f hσ,Germ.coe_compTendsto g hσ]
    exact Germ.coe_mul (f ∘ σ) (g ∘ σ)

private theorem pullPunct_germ (σ : ℂ → ℂ) (hσ : Tendsto σ Punct Punct)
    (f : ℂ → ℂ) : pullPunct σ hσ (Germ.ofFun f) = Germ.ofFun (f ∘ σ) :=
  Germ.coe_compTendsto f hσ

private theorem puncture_pullback (σ : ℂ → ℂ) (ha : AnalyticAt ℂ σ 0) (h0 : σ 0 = 0)
    (hσ : Tendsto σ Punct Punct) (u : Hol (0 : ℂ)) :
    pullPunct σ hσ (punctureHol u) = punctureHol (pullback σ ha h0 u) := by
  obtain ⟨f,hf,he⟩ := u.property
  have hu : u = germ 0 f hf := Subtype.ext he.symm
  rw [hu,punctureHol_germ,pullPunct_germ,pullback_germ,punctureHol_germ]

variable (N : ℕ) [NeZero N] (hN : 5 ≤ N) (c : FiniteCuspEnds318.End N)
variable (p : (OpenJModel318.Base N)[X]) (hRoots : fullRootSet N p) (t : Period)

private theorem chartZeroFraction (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    IsFractionRing (InfinityOrder F) F := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
  letI a0 : Algebra ℂ[X] JField := (basePolynomial 0).toAlgebra
  letI : IsFractionRing ℂ[X] JField := base_fractionRing 0
  letI aF : Algebra ℂ[X] F := (polynomial F 0).toAlgebra
  letI : SMul ℂ[X] JField := a0.toSMul
  letI : SMul JField F := aJ.toSMul
  letI : SMul ℂ[X] F := aF.toSMul
  letI : @IsScalarTower ℂ[X] JField F a0.toSMul aJ.toSMul aF.toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℂ[X] JField F
      inferInstance inferInstance inferInstance a0 aJ aF (by rfl)
  have hpC : (p.map (toComplex N)).Monic := hp.map (toComplex N)
  have hpG : (P N p).Monic := hpC.map (algebraMap Base Generic)
  have hpJ : (pJ N p).Monic := by
    unfold pJ
    letI : Algebra Base (RatFunc ℂ) := SelectedComplexGenericRatFunc318.ratscalar
    exact hpG.map SelectedComplexGenericRatFunc318.ratEquiv.toRingEquiv.toRingHom
  letI : FiniteDimensional JField F := hpJ.finite_adjoinRoot
  exact IsIntegralClosure.isFractionRing_of_finite_extension ℂ[X] JField F (InfinityOrder F)

/-- An actual uniformizer on the original reciprocal compact chart
has first-order analytic readout in that same filled width coordinate.
The cusp coordinate 1/J is not assumed to be an algebraic uniformizer. -/
theorem actual_marked_cusp_uniformizer_order_one
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
    letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
    letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
    letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
      @IsScalarTower.of_algebraMap_eq' ℂ JField F
        inferInstance inferInstance inferInstance aF aJ aC (by rfl)
    letI : Algebra ℂ[X] F := (polynomial F 0).toAlgebra
    let B := InfinityOrder F
    let U := sourceCover F 0
    ∃ (E : F →+* Germ0) (χ : B →+* ℂ) (e : Γ(model F,U.1) ≃+* B),
      let P₀ := RingHom.ker χ
      letI : P₀.IsPrime := RingHom.ker_isPrime χ
      let L := Localization.AtPrime P₀
      let x := U.2.fromSpec
        ((⟨P₀,inferInstance⟩ : PrimeSpectrum B).comap e.toRingHom)
      let R := (model F).presheaf.stalk x
      ∃ (hx : x ∈ U.1) (l : R ≃+* L)
        (β : L →+* F) (Φ : R →+* Hol (0 : ℂ)) (ε : R →+* ℂ),
        CommRingCat.ofHom ((Subalgebra.val B).toRingHom.comp e.toRingHom) =
          (genericMap F).toNormalization.appLE U.1 ⊤ (generic_at_reciprocal_chart F) ≫
            (Scheme.ΓSpecIso (CommRingCat.of F)).hom ∧
        IsDiscreteValuationRing R ∧ Function.Injective Φ ∧
        (∀ z : OrdinaryRoot N p, E (intoWhole N p z) =
          Germ.ofFun (fun q => atCusp N hN c p hRoots t q z)) ∧
        χ.comp (algebraMap ℂ[X] B) = Polynomial.evalRingHom 0 ∧
        (∀ b : B, β (algebraMap B L b) = algebraMap B F b ∧
          ε (l.symm (algebraMap B L b)) = χ b) ∧
        (∀ a : Γ(model F,U.1), l ((model F).presheaf.germ U.1 x hx a) =
          algebraMap B L (e a)) ∧
        punctureHol.comp Φ = E.comp (β.comp l.toRingHom) ∧
        (value (0 : ℂ)).comp Φ = ε ∧
        (∀ r : R, ε r = 0 ↔ l r ∈ IsLocalRing.maximalIdeal L) ∧
        ∀ (π : L) (hi : Irreducible π)
          (hπ : IsLocalRing.maximalIdeal L = Ideal.span ({π} : Set L))
          (f : ℂ → ℂ) (ha : AnalyticAt ℂ f 0),
          Φ (l.symm π) = germ 0 f ha → analyticOrderAt f 0 = 1 := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
  letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
  letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
  letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℂ JField F
      inferInstance inferInstance inferInstance aF aJ aC (by rfl)
  letI : Algebra ℂ[X] F := (polynomial F 0).toAlgebra
  let B := InfinityOrder F
  let U := sourceCover F 0
  obtain ⟨E,χ,e,hx,l,β,Φ,ε,hRead,hDVR,hΦ,hE,hχ,hB,hl,hP,hv,hker⟩ :=
    actual_marked_cusp_scheme_stalk_and_germ N hN c p hRoots t hp hf
  refine ⟨E,χ,e,hx,l,β,Φ,ε,hRead,hDVR,hΦ,hE,hχ,hB,hl,hP,hv,hker,?_⟩
  intro π hi hπ f ha hfG
  let P₀ := RingHom.ker χ
  letI : P₀.IsPrime := RingHom.ker_isPrime χ
  let L := Localization.AtPrime P₀
  let x := U.2.fromSpec
    ((⟨P₀,inferInstance⟩ : PrimeSpectrum B).comap e.toRingHom)
  let R := (model F).presheaf.stalk x
  let G : L →+* Hol (0 : ℂ) := Φ.comp l.symm.toRingHom
  let ε' : L →+* ℂ := ε.comp l.symm.toRingHom
  let scalar : ℂ →+* L :=
    (algebraMap B L).comp ((algebraMap ℂ[X] B).comp Polynomial.C)
  have hFL (v : L) : punctureHol (G v) = E (β v) := by
    have h := RingHom.congr_fun hP (l.symm v)
    change punctureHol (Φ (l.symm v)) = E (β (l (l.symm v))) at h
    rw [l.apply_symm_apply] at h
    exact h
  have hValue (v : L) : value (0 : ℂ) (G v) = ε' v := RingHom.congr_fun hv (l.symm v)
  have hKer (v : L) : ε' v = 0 ↔ v ∈ IsLocalRing.maximalIdeal L := by
    have h := hker (l.symm v)
    rw [l.apply_symm_apply] at h
    exact h
  have hCoeffs := coefficients_at_reciprocal_chart N hN c p hRoots t hf E hE
  have hConstant (z : ℂ) : G (scalar z) = germ 0 (fun _ => z) analyticAt_const := by
    apply punctureHol_injective
    rw [punctureHol_germ,hFL]
    let b : B := algebraMap ℂ[X] B (Polynomial.C z)
    change E (β (algebraMap B L b)) = Germ.ofFun (fun _ => z)
    rw [(hB b).1]
    change E (algebraMap B F (algebraMap ℂ[X] B (Polynomial.C z))) = Germ.ofFun (fun _ => z)
    rw [← IsScalarTower.algebraMap_apply ℂ[X] B F]
    change E (polynomial F 0 (Polynomial.C z)) = Germ.ofFun (fun _ => z)
    exact (RingHom.congr_fun hCoeffs (Polynomial.C z)).trans
      (Germ.coe_eq.mpr (Eventually.of_forall (fun q => Polynomial.eval_C)))
  have hGπ : G π = germ 0 f ha := hfG
  have hz : f 0 = 0 := by
    have hπ0 : ε' π = 0 := (hKer π).mpr
      (hπ.symm ▸ Ideal.mem_span_singleton_self π)
    calc
      f 0 = value (0 : ℂ) (germ 0 f ha) := (value_germ 0 f ha).symm
      _ = value (0 : ℂ) (G π) := congrArg (value (0 : ℂ)) hGπ.symm
      _ = 0 := (hValue π).trans hπ0
  have h1 : analyticOrderAt f 0 ≠ 0 := ha.analyticOrderAt_ne_zero.mpr hz
  have hGi : Function.Injective G := hΦ.comp l.symm.injective
  have hfinite : analyticOrderAt f 0 ≠ ⊤ := by
    intro ht
    apply hi.ne_zero
    apply hGi
    rw [map_zero,hGπ]
    apply Subtype.ext
    exact Germ.coe_eq.mpr (analyticOrderAt_eq_top.mp ht)
  let n := analyticOrderNatAt f 0
  have hn : analyticOrderAt f 0 = n := (Nat.cast_analyticOrderNatAt hfinite).symm
  by_contra hBad
  have hgt : 1 < n := by
    have h0 : n ≠ 0 := fun h => h1 (by rw [hn,h,Nat.cast_zero])
    have h0' : n ≠ 1 := fun h => hBad (by rw [hn,h,Nat.cast_one])
    omega
  obtain ⟨σ,hσ,hσ0,hfix,hne⟩ := analytic_rotation_of_order_gt_one ha hgt hn
  have hpi : pullback σ hσ hσ0 (G π) = G π := by
    rw [hGπ,pullback_germ]
    exact (germ_eq_iff (compose_at_center hσ hσ0 ha) ha).mpr hfix
  have hAll := fixed_of_uniformizer scalar ε' π hKer hπ G hValue hConstant σ hσ hσ0 hpi
  have hσFull : Tendsto σ (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [hσ0] using hσ.continuousAt.tendsto
  have hσP : Tendsto σ Punct Punct := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hσFull.mono_left nhdsWithin_le_nhds,hne.mono (fun q h hs =>
      h.1 (Set.mem_singleton_iff.mp hs))⟩
  have hEG : (pullPunct σ hσP).comp E = E := by
    letI : IsFractionRing B F := chartZeroFraction N p hp hf
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    apply RingHom.ext
    intro b
    let v : L := algebraMap B L b
    have hEv : punctureHol (G v) = E (algebraMap B F b) :=
      (hFL v).trans (congrArg E (hB b).1)
    change pullPunct σ hσP (E (algebraMap B F b)) = E (algebraMap B F b)
    rw [← hEv,puncture_pullback σ hσ hσ0 hσP,hAll v]
  have hSections (z : OrdinaryRoot N p) :
      (fun q => atCusp N hN c p hRoots t (σ q) z) =ᶠ[Punct]
        fun q => atCusp N hN c p hRoots t q z := by
    have h := RingHom.congr_fun hEG (intoWhole N p z)
    change pullPunct σ hσP (E (intoWhole N p z)) = E (intoWhole N p z) at h
    rw [hE z,pullPunct_germ] at h
    exact Germ.coe_eq.mp h
  exact no_moving_symmetry_of_literal_cusp_generators N p hN hRoots t c σ hσP
    (hne.mono (fun _ h => h.2)) (hSections (jSection N p)) (hSections (markedXSection N p))

end SelectedActualMarkedCuspUniformizerOrderOneV2_318

#print axioms SelectedActualMarkedCuspUniformizerOrderOneV2_318.actual_marked_cusp_uniformizer_order_one
