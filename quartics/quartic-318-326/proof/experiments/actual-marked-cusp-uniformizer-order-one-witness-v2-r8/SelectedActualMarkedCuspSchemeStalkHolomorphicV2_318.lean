module

public import SelectedActualMarkedCuspCenterCharacter318
public import SelectedActualCuspCanonicalChartReadout318
public import SelectedActualLocalHolomorphicGerms318
import all SelectedActualLocalHolomorphicGerms318
import Mathlib.RingTheory.Ideal.Maps

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Filter Polynomial Set
open scoped Topology Polynomial
open FiniteCuspEnds318
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexGenericChartClosures318 SelectedActualComplexGenericCompactNormal318
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedCuspPunctureEvaluation318
open SelectedActualMarkedCuspWholeField318 (Germ0)
open SelectedActualMarkedCuspCenterCharacter318
open SelectedActualCuspCanonicalChartReadout318
open SelectedActualLocalHolomorphicGerms318

namespace SelectedActualMarkedCuspSchemeStalkHolomorphicV2_318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

private def punctureFull : Germ (𝓝 (0 : ℂ)) ℂ →+* Germ0 where
  toFun := Germ.map' (fun f : ℂ → ℂ => f)
    (fun _ _ h => h.filter_mono nhdsWithin_le_nhds)
  map_zero' := rfl
  map_one' := rfl
  map_add' u v := Germ.inductionOn₂ u v (fun _ _ => rfl)
  map_mul' u v := Germ.inductionOn₂ u v (fun _ _ => rfl)

/-- Restriction remembers only the same actual puncture coordinate. -/
def punctureHol : Hol (0 : ℂ) →+* Germ0 :=
  punctureFull.comp (Hol (0 : ℂ)).subtype

theorem punctureHol_germ (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    punctureHol (germ 0 f hf) = Germ.ofFun f := by
  rfl

/-- Analytic representatives agreeing on the puncture have equal
center limits and hence the same full holomorphic germ. -/
theorem punctureHol_injective : Function.Injective punctureHol := by
  intro u v huv
  obtain ⟨f,hf,he⟩ := u.property
  obtain ⟨g,hg,he'⟩ := v.property
  have hu : u = germ 0 f hf := Subtype.ext he.symm
  have hv : v = germ 0 g hg := Subtype.ext he'.symm
  rw [hu,hv,punctureHol_germ f hf,punctureHol_germ g hg] at huv
  have hp : f =ᶠ[𝓝[≠] (0 : ℂ)] g := Germ.coe_eq.mp huv
  have h0 : f 0 = g 0 := tendsto_nhds_unique
    (hf.continuousAt.continuousWithinAt.tendsto)
    (hg.continuousAt.continuousWithinAt.tendsto.congr' hp.symm)
  have hA : f =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [eventually_nhdsWithin_iff.mp hp] with q hq
    by_cases h : q = 0
    · exact h.symm ▸ h0
    · exact hq (fun h' => h (Set.mem_singleton_iff.mp h'))
  rw [hu,hv]
  exact (germ_eq_iff hf hg).mpr hA

private theorem order_ring_lift
    {T : Type*} [CommRing T] (e : T →+* Germ0) (χ : T →+* ℂ)
    (H : ∀ b : T, ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ e b = Germ.ofFun f ∧ f 0 = χ b) :
    ∃ E : T →+* Hol (0 : ℂ), punctureHol.comp E = e ∧ (value (0 : ℂ)).comp E = χ := by
  classical
  choose f hf hE hχ using H
  let G := fun b : T => germ 0 (f b) (hf b)
  have hP (b : T) : punctureHol (G b) = e b :=
    (punctureHol_germ (f b) (hf b)).trans (hE b).symm
  let E : T →+* Hol (0 : ℂ) := {
    toFun := G
    map_zero' := punctureHol_injective (by rw [hP (0 : T),map_zero e,map_zero punctureHol])
    map_one' := punctureHol_injective (by rw [hP (1 : T),map_one e,map_one punctureHol])
    map_add' a b := punctureHol_injective (by
      rw [map_add punctureHol,hP (a+b),hP a,hP b,map_add e])
    map_mul' a b := punctureHol_injective (by
      rw [map_mul punctureHol,hP (a*b),hP a,hP b,map_mul e]) }
  refine ⟨E,RingHom.ext hP,RingHom.ext (fun b => ?_)⟩
  change value (0 : ℂ) (germ 0 (f b) (hf b)) = χ b
  exact (value_germ 0 (f b) (hf b)).trans (hχ b)

private theorem hol_unit_of_nonzero_value (v : Hol (0 : ℂ))
    (hv : value (0 : ℂ) v ≠ 0) : IsUnit v := by
  obtain ⟨f,hf,he⟩ := v.property
  have hfG : v = germ 0 f hf := Subtype.ext he.symm
  have h₀ : f 0 ≠ 0 := by rwa [hfG,value_germ] at hv
  rw [hfG]
  exact germ_isUnit hf h₀

section SchemeChart

variable {T F : Type} [CommRing T] [Field F]
variable {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
variable (e : Γ(X,U) ≃+* T) (P : Ideal T) [P.IsPrime]

private abbrev chartPrime : PrimeSpectrum Γ(X,U) :=
  (⟨P, inferInstance⟩ : PrimeSpectrum T).comap e.toRingHom

private theorem chart_mem : hU.fromSpec (chartPrime e P) ∈ U := by
  have hx : hU.fromSpec (chartPrime e P) ∈ Set.range hU.fromSpec :=
    Set.mem_range_self _
  rwa [hU.range_fromSpec] at hx

private theorem actual_affine_stalk :
    ∃ l : (X.presheaf.stalk (hU.fromSpec (chartPrime e P))) ≃+* Localization.AtPrime P,
      ∀ a : Γ(X,U),
        l (X.presheaf.germ U _ (chart_mem hU e P) a) =
          algebraMap T (Localization.AtPrime P) (e a) := by
  let y := chartPrime e P
  let x := hU.fromSpec y
  let hx : x ∈ U := chart_mem hU e P
  let R := X.presheaf.stalk x
  letI : Algebra Γ(X,U) R := X.presheaf.algebra_section_stalk ⟨x,hx⟩
  letI : IsLocalization.AtPrime R y.asIdeal := hU.isLocalization_stalk' y hx
  have hE : y.asIdeal.primeCompl.map e.toMonoidHom = P.primeCompl :=
    RingEquiv.map_primeCompl_comap_eq e P
  let l : R ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv R (Localization.AtPrime P) e hE
  exact ⟨l,fun a => IsLocalization.ringEquivOfRingEquiv_eq hE a⟩

private theorem actual_chart_point_nongeneric [IsIntegral X]
    (hDom : IsDomain Γ(X,U)) (hP : P ≠ ⊥) :
    hU.fromSpec (chartPrime e P) ≠ genericPoint X := by
  letI := hDom
  let x := hU.fromSpec (chartPrime e P)
  letI : Nonempty U := ⟨⟨x,chart_mem hU e P⟩⟩
  intro h
  let hx : genericPoint X ∈ U := h ▸ chart_mem hU e P
  have he : hU.fromSpec (hU.primeIdealOf ⟨genericPoint X,hx⟩) =
      hU.fromSpec (chartPrime e P) :=
    (hU.fromSpec_primeIdealOf _).trans h.symm
  have he' : chartPrime e P = hU.primeIdealOf ⟨genericPoint X,hx⟩ :=
    hU.fromSpec.isOpenEmbedding.injective he.symm
  rw [hU.primeIdealOf_genericPoint,genericPoint_eq_bot_of_affine] at he'
  apply hP
  apply le_antisymm _ bot_le
  intro b hb
  apply Ideal.mem_bot.mpr
  have hbe : e.symm b ∈ (chartPrime e P).asIdeal := by
    change e (e.symm b) ∈ P
    rw [e.apply_symm_apply]
    exact hb
  rw [he'] at hbe
  have hz : e.symm b = 0 := Ideal.mem_bot.mp hbe
  exact e.symm.injective (hz.trans (map_zero e.symm).symm)

end SchemeChart

private theorem cusp_kernel_nonzero
    (F : Type) [Field F] [Algebra JField F] (χ : InfinityOrder F →+* ℂ)
    (hχ : χ.comp (algebraMap ℂ[X] (InfinityOrder F)) = Polynomial.evalRingHom 0) :
    RingHom.ker χ ≠ ⊥ := by
  letI : Algebra ℂ[X] F := (polynomial F 0).toAlgebra
  let B := InfinityOrder F
  let a : B := algebraMap ℂ[X] B X
  have ha : a ∈ RingHom.ker χ := by
    change χ a = 0
    exact (RingHom.congr_fun hχ X).trans Polynomial.eval_X
  have hi : Function.Injective (polynomial F 0) := by
    letI : Algebra ℂ[X] JField := (basePolynomial 0).toAlgebra
    letI : IsFractionRing ℂ[X] JField := base_fractionRing 0
    exact (algebraMap JField F).injective.comp (IsFractionRing.injective ℂ[X] JField)
  intro hp
  have h0 : a = 0 := Ideal.mem_bot.mp (hp ▸ ha)
  have he := congrArg (algebraMap B F) h0
  change algebraMap B F (algebraMap ℂ[X] B X) = algebraMap B F 0 at he
  rw [← IsScalarTower.algebraMap_apply ℂ[X] B F,map_zero] at he
  exact Polynomial.X_ne_zero (hi (he.trans (map_zero (polynomial F 0)).symm))

variable (N : ℕ) [NeZero N] (hN : 5 ≤ N) (c : FiniteCuspEnds318.End N)
variable (p : (OpenJModel318.Base N)[X]) (hRoots : fullRootSet N p) (t : Period)

/-- The cusp character selects the actual chart-0 point of the original
whole-field normalization, and the actual scheme DVR embeds into the
holomorphic germs of its exact width coordinate. Residue and generic
restriction are on this same local ring. No uniformizer order or global
filling identification is assumed or claimed here. -/
theorem actual_marked_cusp_scheme_stalk_and_germ
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
        (∀ r : R, ε r = 0 ↔ l r ∈ IsLocalRing.maximalIdeal L) := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI aJ : Algebra JField F := AdjoinRoot.instAlgebra (S := JField) (pJ N p)
  letI aF : Algebra ℂ JField := RatFunc.instAlgebraOfPolynomial ℂ ℂ
  letI aC : Algebra ℂ F := AdjoinRoot.instAlgebra (S := ℂ) (pJ N p)
  letI tC : @IsScalarTower ℂ JField F aF.toSMul aJ.toSMul aC.toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℂ JField F
      inferInstance inferInstance inferInstance aF aJ aC (by rfl)
  letI : Algebra ℂ[X] F := (polynomial F 0).toAlgebra
  letI : IsIntegral (model F) := model_integral F
  let B := InfinityOrder F
  let U := sourceCover F 0
  obtain ⟨E,χ,hEinj,hEord,hχ0,hχsurj,hχ⟩ :=
    actual_marked_cusp_center N hN c p hRoots t hp hf
  let P₀ := RingHom.ker χ
  letI : P₀.IsPrime := RingHom.ker_isPrime χ
  let L := Localization.AtPrime P₀
  obtain ⟨e,hRead⟩ := exists_actual_reciprocal_chart_with_readout F
  let x := U.2.fromSpec (chartPrime e P₀)
  let hx : x ∈ U.1 := chart_mem U.2 e P₀
  let R := (model F).presheaf.stalk x
  obtain ⟨l,hl⟩ := actual_affine_stalk U.2 e P₀
  have hng : x ≠ genericPoint (model F) :=
    actual_chart_point_nongeneric U.2 e P₀ (MulEquiv.isDomain _ e.toMulEquiv)
      (cusp_kernel_nonzero F χ hχ0)
  have hDVR : IsDiscreteValuationRing R :=
    (literal_projective_normalization N p hp hf).2 x hng
  let eB := E.comp (algebraMap B F)
  obtain ⟨G,hGP,hGv⟩ := order_ring_lift eB χ hχ
  have hχne (s : P₀.primeCompl) : χ s ≠ 0 := Ideal.mem_primeCompl_iff.mp s.property
  have hDen (s : P₀.primeCompl) : IsUnit (G s) :=
    hol_unit_of_nonzero_value (G s) (fun h => hχne s ((RingHom.congr_fun hGv s).symm.trans h))
  have hBi : Function.Injective (algebraMap B F) := IsIntegralClosure.algebraMap_injective B ℂ[X] F
  have hFden (s : P₀.primeCompl) : IsUnit (algebraMap B F s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have h0 : (s : B) = 0 := hBi (hz.trans (map_zero (algebraMap B F)).symm)
    exact hχne s ((congrArg χ h0).trans (map_zero χ))
  let ΦL : L →+* Hol (0 : ℂ) := IsLocalization.lift (g := G) hDen
  let β : L →+* F := IsLocalization.lift (g := algebraMap B F) hFden
  have hGβ (b : B) : ΦL (algebraMap B L b) = G b := IsLocalization.lift_eq hDen b
  have hβ (b : B) : β (algebraMap B L b) = algebraMap B F b := IsLocalization.lift_eq hFden b
  have hβi : Function.Injective β := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (S := L) P₀.primeCompl β).mpr
    intro a b
    rw [hβ a,hβ b]
    exact ⟨fun h => (hβ a).symm.trans ((congrArg β h).trans (hβ b)),
      fun h => congrArg (algebraMap B L) (hBi h)⟩
  have hpGL : punctureHol.comp ΦL = E.comp β := by
    apply IsLocalization.ringHom_ext P₀.primeCompl
    apply RingHom.ext
    intro b
    change punctureHol (ΦL (algebraMap B L b)) = E (β (algebraMap B L b))
    rw [hGβ,hβ]
    exact RingHom.congr_fun hGP b
  let εL : L →+* ℂ := (value (0 : ℂ)).comp ΦL
  have hεL (b : B) : εL (algebraMap B L b) = χ b := by
    change value (0 : ℂ) (ΦL (algebraMap B L b)) = χ b
    rw [hGβ]
    exact RingHom.congr_fun hGv b
  have hχunit (s : P₀.primeCompl) : IsUnit (χ s) := isUnit_iff_ne_zero.mpr (hχne s)
  have hεLift : εL = IsLocalization.lift (M := P₀.primeCompl) (g := χ) hχunit := by
    apply IsLocalization.ringHom_ext P₀.primeCompl
    apply RingHom.ext
    intro b
    exact (hεL b).trans (IsLocalization.lift_eq hχunit b).symm
  have hker (z : L) : εL z = 0 ↔ z ∈ IsLocalRing.maximalIdeal L := by
    obtain ⟨b,s,rfl⟩ := IsLocalization.exists_mk'_eq P₀.primeCompl z
    have hLift : εL (IsLocalization.mk' L b s) = 0 ↔ χ b = χ s * 0 := by
      rw [hεLift]
      exact IsLocalization.lift_mk'_spec (S := L) hχunit b 0 s
    have hmem : IsLocalization.mk' L b s ∈ IsLocalRing.maximalIdeal L ↔ b ∈ P₀ :=
      IsLocalization.AtPrime.mk'_mem_maximal_iff L P₀ b s
    have hzero : χ b = χ s * 0 ↔ b ∈ P₀ := by
      rw [mul_zero] <;> rfl
    exact (hLift.trans hzero).trans hmem.symm
  let Φ : R →+* Hol (0 : ℂ) := ΦL.comp l.toRingHom
  let ε : R →+* ℂ := εL.comp l.toRingHom
  have hΦi : Function.Injective Φ := by
    intro x y hxy
    apply l.injective
    apply hβi
    apply hEinj
    exact (RingHom.congr_fun hpGL (l x)).symm.trans
      ((congrArg punctureHol hxy).trans (RingHom.congr_fun hpGL (l y)))
  refine ⟨E,χ,e,hx,l,β,Φ,ε,hRead,hDVR,hΦi,hEord,hχ0,?_,hl,?_,?_,fun r => hker (l r)⟩
  · intro b
    refine ⟨hβ b,?_⟩
    change εL (l (l.symm (algebraMap B L b))) = χ b
    rw [l.apply_symm_apply]
    exact hεL b
  · apply RingHom.ext
    intro r
    exact RingHom.congr_fun hpGL (l r)
  · apply RingHom.ext
    intro r
    rfl

end SelectedActualMarkedCuspSchemeStalkHolomorphicV2_318

#print axioms SelectedActualMarkedCuspSchemeStalkHolomorphicV2_318.actual_marked_cusp_scheme_stalk_and_germ
