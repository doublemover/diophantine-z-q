module

public import SelectedActualMarkedEllipticLocalHolomorphicGerm318
public import SelectedActualEllipticFixedGermCore318
public import SelectedActualEllipticAnalyticRotation318
public import SelectedActualMarkedPunctureSeparation318
import all SelectedActualMarkedEllipticCenterCharacter318
import all SelectedActualMarkedEllipticFieldContinuation318
import all SelectedActualWholeMarkedOrdinaryMeromorphicGerm318

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Filter Polynomial
open scoped Polynomial Topology
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexGenericChartClosures318 SelectedActualComplexGenericCompactNormal318
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualLiteralMarkedGenericTensor318 (ordinaryFieldAlgebra)
open SelectedActualLiteralMarkedOrdinaryNormalization318 (B O)
open SelectedActualComplexWholeRootField318 (Period)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedEllipticCenterCharacter318
open SelectedActualMarkedEllipticFieldContinuation318
open SelectedActualMarkedPunctureSeparation318 (local_fine_chart_eq_of_marked_coordinates_eq)
open SelectedActualLocalHolomorphicGerms318 SelectedActualEllipticFixedGermCore318
open SelectedActualEllipticAnalyticRotation318
open SelectedActualMarkedEllipticLocalHolomorphicGerm318
open OpenJLocalComparison318 (j)
open GammaOneAtlas318 GammaOneFiber318

namespace SelectedActualMarkedEllipticUniformizerOrderOne318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hRoots : fullRootSet N p)

private theorem chart_target_center (hN : 5 ≤ N) (τ : UpperHalfPlane) :
    (τ : ℂ) ∈ (HolomorphicCharts318.localChart N hN τ).target := by
  have h := (HolomorphicCharts318.localChart N hN τ).map_source
    (HolomorphicCharts318.localChart_center N hN τ)
  have he : HolomorphicCharts318.localChart N hN τ (quotientMap N τ) = (τ : ℂ) := by
    rw [HolomorphicCharts318.localChart_apply]
    exact congrArg (fun x : UpperHalfPlane => (x : ℂ))
      ((quotient_localHomeomorph N hN).localInverseAt_apply_self (x := τ))
  exact he ▸ h

section Affine

variable {F : Type} [Field F] [Algebra JField F]
variable (t : Period) (e : OrdinaryRoot N p ≃ₐ[Base] O F)

private def ordinaryEval (w : ℂ) : O F →+* ℂ :=
  (atDisk N p hRoots t w).comp e.symm.toRingHom

private theorem ordinaryEval_comp (w : ℂ) (b : B F) :
    ordinaryEval N p hRoots t e w (algebraMap (B F) (O F) b) =
      puncturedChartEvaluation N p hRoots t e w b := by
  unfold ordinaryEval puncturedChartEvaluation
  rfl

private theorem marked_x_eval (w : ℂ)
    (hw : OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex w)) :
    ordinaryEval N p hRoots t e w (e (AdjoinRoot.root (pC N p))) =
      SelectedMarkedPeriodCoordinate318.arithmeticX N (UpperHalfPlane.ofComplex w) := by
  unfold ordinaryEval
  rw [RingHom.comp_apply]
  change atDisk N p hRoots t w (e.symm (e (AdjoinRoot.root (pC N p)))) = _
  rw [e.symm_apply_apply,atDisk_of_admissible N p hRoots t w hw,atPeriod_root] <;> rfl

/-- Source-separation needs only finitely many ordinary readouts:
J, and one numerator and denominator of the same literal original x.
There is no simultaneous neighborhood assertion for all sections. -/
theorem no_nontrivial_local_symmetry_of_original_sections
    (hN : 5 ≤ N) (τ : UpperHalfPlane) (σ : ℂ → ℂ)
    (htσ : Tendsto σ (𝓝 (τ : ℂ)) (𝓝 (τ : ℂ)))
    (hne : ∀ᶠ w in 𝓝[≠] (τ : ℂ), σ w ≠ (τ : ℂ) ∧ σ w ≠ w)
    (hfixed : ∀ b : B F, ∀ᶠ w in 𝓝[≠] (τ : ℂ),
      puncturedChartEvaluation N p hRoots t e (σ w) b =
        puncturedChartEvaluation N p hRoots t e w b) : False := by
  letI : Algebra ℂ[X] F := (polynomial F 1).toAlgebra
  let C := HolomorphicCharts318.localChart N hN τ
  let ψ := puncturedChartEvaluation N p hRoots t e
  let A := Algebra.algebraMapSubmonoid (B F) (Submonoid.powers denominator)
  let x := e (AdjoinRoot.root (pC N p))
  obtain ⟨⟨b,s⟩,hbs⟩ := IsLocalization.surj A x
  let d : B F := s
  let J : B F := algebraMap ℂ[X] (B F) Polynomial.X
  have hC : ∀ᶠ w in 𝓝 (τ : ℂ), w ∈ C.target :=
    C.open_target.mem_nhds (chart_target_center N hN τ)
  have hOrd := eventually_ordinary_in_punctured_period τ
  have hOrdσ₀ := htσ.eventually (eventually_nhdsWithin_iff.mp hOrd)
  have contra : ∀ᶠ w in 𝓝[≠] (τ : ℂ), False := by
    filter_upwards [hne,hC.filter_mono nhdsWithin_le_nhds,
      (htσ.eventually hC).filter_mono nhdsWithin_le_nhds,hOrd,
      hOrdσ₀.filter_mono nhdsWithin_le_nhds,hfixed J,hfixed b,hfixed d]
      with w hw htw hts hwo hcond hJ hb hd
    have hso : OpenJComplexEvaluation318.Admissible (UpperHalfPlane.ofComplex (σ w)) :=
      hcond (fun h => hw.1 (Set.mem_singleton_iff.mp h))
    have hJw : ψ w J = j w :=
      (RingHom.congr_fun (chart_polynomial_evaluation N p hRoots t e w hwo) Polynomial.X).trans
        Polynomial.eval_X
    have hJs : ψ (σ w) J = j (σ w) :=
      (RingHom.congr_fun (chart_polynomial_evaluation N p hRoots t e (σ w) hso) Polynomial.X).trans
        Polynomial.eval_X
    let Ew := ordinaryEval N p hRoots t e w
    let Es := ordinaryEval N p hRoots t e (σ w)
    have hew : Ew x * Ew (algebraMap (B F) (O F) d) = ψ w b := by
      have h := congrArg Ew hbs
      change Ew (x * algebraMap (B F) (O F) d) = Ew (algebraMap (B F) (O F) b) at h
      rw [map_mul,ordinaryEval_comp] at h
      exact h
    have hes : Es x * Es (algebraMap (B F) (O F) d) = ψ (σ w) b := by
      have h := congrArg Es hbs
      change Es (x * algebraMap (B F) (O F) d) = Es (algebraMap (B F) (O F) b) at h
      rw [map_mul,ordinaryEval_comp] at h
      exact h
    have hden : Es (algebraMap (B F) (O F) d) = Ew (algebraMap (B F) (O F) d) :=
      (ordinaryEval_comp N p hRoots t e (σ w) d).trans
        (hd.trans (ordinaryEval_comp N p hRoots t e w d).symm)
    have hdn : Ew (algebraMap (B F) (O F) d) ≠ 0 :=
      ((IsLocalization.map_units (O F) s).map Ew).ne_zero
    have hX : Es x = Ew x :=
      mul_right_cancel₀ hdn <| (congrArg (Es x * ·) hden.symm).trans
        (hes.trans (hb.trans hew.symm))
    apply hw.2
    exact local_fine_chart_eq_of_marked_coordinates_eq N hN τ (σ w) w
      hts htw hso hwo (hJs.symm.trans (hJ.trans hJw))
      ((marked_x_eval N p hRoots t e (σ w) hso).symm.trans
        (hX.trans (marked_x_eval N p hRoots t e w hwo)))
  exact (Filter.NeBot.ne inferInstance) (Filter.eventually_false_iff_eq_bot.mp contra)

end Affine

/-- For the exact elliptic branch and original compact stalk, every
uniformizer has first-order analytic readout in the same original
fine coordinate. This is not claiming that the ramified J-J(τ)
itself is an algebraic uniformizer. -/
theorem actual_marked_elliptic_uniformizer_order_one
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
  obtain ⟨t,e,χ,hx,l,Φ,ε,H,hDVR,hΦ,hε,hBase,hker,hl,hβ,hConst⟩ :=
    actual_marked_elliptic_stalk_holomorphic_germ N p hRoots hN τ hp hd hf
  refine ⟨t,e,χ,hx,l,Φ,H,hDVR,hl,hβ,?_⟩
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
    apply Subtype.ext
    exact Germ.coe_eq.mpr (analyticOrderAt_eq_top.mp ht)
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

end SelectedActualMarkedEllipticUniformizerOrderOne318

#print axioms SelectedActualMarkedEllipticUniformizerOrderOne318.no_nontrivial_local_symmetry_of_original_sections
#print axioms SelectedActualMarkedEllipticUniformizerOrderOne318.actual_marked_elliptic_uniformizer_order_one
