module

public import SelectedActualMarkedCuspWholeField318
import all SelectedActualLiteralComplexCompactStalkDVR318
import all SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Coeff

public section
noncomputable section

open Filter Set Polynomial
open scoped Polynomial Topology
open FiniteCuspEnds318
open SelectedComplexOrdinaryBase318 SelectedComplexOrdinaryOneField318
open SelectedActualComplexWholeRootField318 (Period)
open SelectedComplexGenericRatFunc318 SelectedActualComplexGenericChartClosures318
open SelectedActualLiteralComplexCompactStalkDVR318
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open SelectedActualMarkedCuspPunctureEvaluation318
open SelectedActualMarkedCuspWholeField318

namespace SelectedActualMarkedCuspCenterCharacter318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The actual reciprocal normal order for the same whole generic field.
The polynomial variable is 1/J, via the existing chart 0 map. -/
abbrev InfinityOrder (F : Type) [Field F] [Algebra JField F] :=
  letI : Algebra ℂ[X] F := (polynomial F 0).toAlgebra
  integralClosure ℂ[X] F

private theorem polynomial_family_continuous (P : ℂ[X][X]) :
    Continuous (fun v : ℂ × ℂ => P.eval₂ (evalRingHom v.1) v.2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have h : (fun v : ℂ × ℂ => (P + Q).eval₂ (evalRingHom v.1) v.2) =
        (fun v => P.eval₂ (evalRingHom v.1) v.2) +
        (fun v => Q.eval₂ (evalRingHom v.1) v.2) := by
      funext v
      rw [Pi.add_apply,Polynomial.eval₂_add]
    rw [h]
    exact hP.add hQ
  | monomial n a =>
    let b : ℂ × ℂ → ℂ := (fun v : ℂ => a.eval v) ∘ Prod.fst
    have h : (fun v : ℂ × ℂ => (Polynomial.monomial n a).eval₂
        (evalRingHom v.1) v.2) = b * (Prod.snd : ℂ × ℂ → ℂ)^n := by
      funext v
      rw [Pi.mul_apply,Pi.pow_apply,Polynomial.eval₂_monomial] <;> rfl
    rw [h]
    exact ((Polynomial.continuous a).comp continuous_fst).mul (continuous_snd.pow n)

/-- A monic family along a continuous base cannot have roots tending
to infinity. Reverse the polynomial and evaluate near (U(0),0). -/
private theorem eventually_bounded_monic_roots
    (U f : ℂ → ℂ) (hU : ContinuousAt U 0)
    (P : ℂ[X][X]) (hP : P.Monic)
    (hRoot : ∀ᶠ q in 𝓝[≠] (0 : ℂ), P.eval₂ (evalRingHom (U q)) (f q) = 0) :
    ∃ R : ℝ, ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖f q‖ ≤ R := by
  let Rv := fun v : ℂ × ℂ => P.reverse.eval₂ (evalRingHom v.1) v.2
  have h1 : Rv (U 0,0) = 1 := by
    change P.reverse.eval₂ (evalRingHom (U 0)) 0 = 1
    rw [Polynomial.eval₂_at_zero,Polynomial.coeff_zero_reverse,hP.leadingCoeff,map_one]
  have hC : ContinuousAt Rv (U 0,0) :=
    (polynomial_family_continuous P.reverse).continuousAt
  have hN : {v | Rv v ≠ 0} ∈ 𝓝 (U 0,(0 : ℂ)) :=
    hC.eventually_ne (by rw [h1]; exact one_ne_zero)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hN
  have hnear : ∀ᶠ q in 𝓝 (0 : ℂ), U q ∈ Metric.ball (U 0) δ :=
    hU.eventually (Metric.ball_mem_nhds _ hδ)
  refine ⟨δ⁻¹,?_⟩
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,hRoot] with q hq hroot
  by_contra! hbig
  have hf0 : f q ≠ 0 := by
    intro hz
    rw [hz,norm_zero] at hbig
    exact (not_lt_of_ge (inv_pos.mpr hδ).le) hbig
  have hinv : ‖(f q)⁻¹‖ < δ := by
    rw [norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr hf0) hδ).mpr hbig
  have hp : (U q,(f q)⁻¹) ∈ Metric.ball (U 0,(0 : ℂ)) δ := by
    change dist (U q,(f q)⁻¹) (U 0,(0 : ℂ)) < δ
    rw [Prod.dist_eq,dist_zero_right,max_lt_iff]
    exact ⟨Metric.mem_ball.mp hq,hinv⟩
  have hnr : P.reverse.eval₂ (evalRingHom (U q)) (f q)⁻¹ ≠ 0 := by
    have hh := hball hp
    change P.reverse.eval₂ (evalRingHom (U q)) (f q)⁻¹ ≠ 0 at hh
    exact hh
  apply hnr
  letI : Invertible (f q) := invertibleOfNonzero hf0
  rw [← invOf_eq_inv]
  exact (Polynomial.eval₂_reverse_eq_zero_iff (evalRingHom (U q)) (f q) P).mpr hroot

private theorem holomorphic_germ_of_bounded
    (f : ℂ → ℂ) (hf : ∀ᶠ q in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ f q)
    (hb : ∃ R : ℝ, ∀ᶠ q in 𝓝[≠] (0 : ℂ), ‖f q‖ ≤ R) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ (f : Germ0) = Germ.ofFun g := by
  obtain ⟨R,hR⟩ := hb
  have hN : {q : ℂ | q ∈ ({0} : Set ℂ)ᶜ →
      AnalyticAt ℂ f q ∧ ‖f q‖ ≤ R} ∈ 𝓝 (0 : ℂ) :=
    eventually_nhdsWithin_iff.mp (hf.and hR)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hN
  let S : Set ℂ := Metric.ball 0 δ
  have hs : S ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hδ
  have hA : DifferentiableOn ℂ f (S \ ({0} : Set ℂ)) := by
    intro q hq
    exact (hball hq.1 hq.2).1.differentiableAt.differentiableWithinAt
  have hB : BddAbove ((norm ∘ f) '' (S \ ({0} : Set ℂ))) := by
    refine ⟨R,?_⟩
    rintro _ ⟨q,hq,rfl⟩
    exact (hball hq.1 hq.2).2
  let g := Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f)
  have hg : AnalyticAt ℂ g 0 :=
    (Complex.differentiableOn_update_limUnder_of_bddAbove hs hA hB).analyticAt hs
  refine ⟨g,hg,Germ.coe_eq.mpr ?_⟩
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hn : q ≠ (0 : ℂ) := fun h => hq (Set.mem_singleton_iff.mpr h)
  change f q = Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f) q
  rw [Function.update_of_ne hn]

variable (N : ℕ) [NeZero N] (hN : 5 ≤ N) (c : End N)
variable (p : (OpenJModel318.Base N)[X]) (hRoots : fullRootSet N p)
variable (t : Period)

abbrev cuspJ := AllCuspJPole318.localJ (AllCuspQJ318.natWidth N hN c)
abbrev cuspU := fun q : ℂ => (cuspJ N hN c q)⁻¹

theorem cuspU_holomorphic : AnalyticAt ℂ (cuspU N hN c) 0 := by
  let w := AllCuspQJ318.natWidth N hN c
  have hU : cuspU N hN c = (fun q : ℂ => q^w / AllCuspJPole318.numerator w q) := by
    funext q
    change (AllCuspJPole318.numerator w q / q^w)⁻¹ =
      q^w / AllCuspJPole318.numerator w q
    exact inv_div _ _
  rw [hU]
  exact AllCuspJPole318.reciprocal_analytic w (AllCuspQJ318.natWidth_pos N hN c)

theorem cuspU_zero : cuspU N hN c 0 = 0 := by
  simp only [cuspU,cuspJ,AllCuspJPole318.localJ,
    zero_pow (Nat.ne_of_gt (AllCuspQJ318.natWidth_pos N hN c)),div_zero,inv_zero]

private theorem intoWhole_of_base (a : Base) :
    letI : Algebra Base JField := ratscalar
    intoWhole N p (AdjoinRoot.of (pC N p) a) =
      AdjoinRoot.of (pJ N p) (algebraMap Base JField a) := by
  letI : Algebra Base JField := ratscalar
  have h : intoGeneric N p (AdjoinRoot.of (pC N p) a) =
      AdjoinRoot.of (P N p) (algebraMap Base Generic a) := by
    unfold intoGeneric
    exact AdjoinRoot.map_of _ _ _ _ _
  unfold intoWhole
  rw [RingHom.comp_apply,h]
  change AdjoinRoot.map ratEquiv.toRingEquiv.toRingHom (P N p) (pJ N p)
    (pJ_associated N p).symm.dvd (AdjoinRoot.of (P N p) (algebraMap Base Generic a)) = _
  exact (AdjoinRoot.map_of _ _ _ _ _).trans
    (congrArg (AdjoinRoot.of (pJ N p)) (ratEquiv.commutes a))

private def funAlg (U : ℂ → ℂ) : ℂ[X] →+* (ℂ → ℂ) where
  toFun a q := a.eval (U q)
  map_zero' := funext (fun q => Polynomial.eval_zero)
  map_one' := funext (fun q => Polynomial.eval_one)
  map_add' a b := funext (fun q => Polynomial.eval_add)
  map_mul' a b := funext (fun q => Polynomial.eval_mul)

private def polynomialGerm (U : ℂ → ℂ) : ℂ[X] →+* Germ0 :=
  (Germ.coeRingHom (𝓝[≠] (0 : ℂ))).comp (funAlg U)

private theorem coefficients_at_reciprocal_chart
    (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    ∀ (E : F →+* Germ0),
      (∀ z : OrdinaryRoot N p, E (intoWhole N p z) =
        Germ.ofFun (fun q => atCusp N hN c p hRoots t q z)) →
      E.comp (polynomial F 0) = polynomialGerm (cuspU N hN c) := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra Base JField := ratscalar
  letI : IsScalarTower ℂ[X] Base JField := rattower
  change ∀ (E : F →+* Germ0),
    (∀ z : OrdinaryRoot N p, E (intoWhole N p z) =
      Germ.ofFun (fun q => atCusp N hN c p hRoots t q z)) →
    E.comp (polynomial F 0) = polynomialGerm (cuspU N hN c)
  intro E he
  have hBA : basePolynomial 1 = algebraMap ℂ[X] JField := by simp [basePolynomial]
  have hB (a : ℂ[X]) :
      intoWhole N p (AdjoinRoot.of (pC N p) (algebraMap ℂ[X] Base a)) = polynomial F 1 a := by
    rw [intoWhole_of_base N p]
    change AdjoinRoot.of (pJ N p) (algebraMap Base JField (algebraMap ℂ[X] Base a)) =
      AdjoinRoot.of (pJ N p) (basePolynomial 1 a)
    rw [← IsScalarTower.algebraMap_apply ℂ[X] Base JField,hBA]
  have hE (a : ℂ[X]) : E (polynomial F 1 a) = polynomialGerm (cuspJ N hN c) a := by
    rw [← hB a,he]
    apply Germ.coe_eq.mpr
    exact original_cusp_polynomial_evaluation N hN c p hRoots t a
  apply Polynomial.ringHom_ext
  · intro z
    change E (polynomial F 0 (C z)) = polynomialGerm (cuspU N hN c) (C z)
    rw [polynomial_C F 0,← polynomial_C F 1,hE]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun q => (Polynomial.eval_C).trans Polynomial.eval_C.symm)
  · change E (polynomial F 0 X) = polynomialGerm (cuspU N hN c) X
    have hJ : E (coordinate F) = Germ.ofFun (cuspJ N hN c) := by
      rw [← polynomial_X₁ F]
      exact (hE X).trans (Germ.coe_eq.mpr <| Eventually.of_forall (fun q => Polynomial.eval_X))
    let J : Germ0 := Germ.ofFun (cuspJ N hN c)
    let U : Germ0 := Germ.ofFun (cuspU N hN c)
    have hUJ : U * J = 1 := by
      change Germ.ofFun (fun q => cuspU N hN c q * cuspJ N hN c q) =
        Germ.ofFun (fun _ => (1 : ℂ))
      apply Germ.coe_eq.mpr
      filter_upwards [eventually_ordinary_at_original_cusp N hN c] with q hq
      have hz : cuspJ N hN c q ≠ 0 := by
        rw [← literal_j_of_originalCuspLift N hN c q hq.1]
        exact hq.2.1
      exact inv_mul_cancel₀ hz
    have hUnit : IsUnit J :=
      ⟨Units.mkOfMulEqOne J U ((mul_comm J U).trans hUJ),rfl⟩
    have h0 : E (polynomial F 0 X) * J = 1 := by
      rw [← hJ,← map_mul,polynomial_X₀,inv_mul_cancel₀ (coordinate_ne_zero F),map_one]
    have hX : polynomialGerm (cuspU N hN c) X = U :=
      Germ.coe_eq.mpr (Eventually.of_forall (fun q => Polynomial.eval_X))
    rw [hX]
    exact (IsUnit.mul_left_inj hUnit).mp (h0.trans hUJ.symm)

private theorem center_character_of_holomorphic_values
    {T : Type*} [CommRing T] (E : T →+* Germ0)
    (H : ∀ b : T, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ E b = Germ.ofFun g) :
    ∃ χ : T →+* ℂ, ∀ b : T, ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧ E b = Germ.ofFun g ∧ g 0 = χ b := by
  classical
  choose g hg he using H
  have hlim (b : T) : Tendsto (g b) (𝓝[≠] (0 : ℂ)) (𝓝 (g b 0)) :=
    (hg b).continuousAt.continuousWithinAt.tendsto
  have h0 : g 0 =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 :=
    Germ.coe_eq.mp ((he 0).symm.trans (map_zero E))
  have h1 : g 1 =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 1 :=
    Germ.coe_eq.mp ((he 1).symm.trans (map_one E))
  have hadd (a b : T) : g (a+b) =ᶠ[𝓝[≠] (0 : ℂ)] fun q => g a q + g b q := by
    apply Germ.coe_eq.mp
    rw [← he (a+b),map_add,he a,he b] <;> rfl
  have hmul (a b : T) : g (a*b) =ᶠ[𝓝[≠] (0 : ℂ)] fun q => g a q * g b q := by
    apply Germ.coe_eq.mp
    rw [← he (a*b),map_mul,he a,he b] <;> rfl
  let χ : T →+* ℂ := {
    toFun := fun b => g b 0
    map_zero' := tendsto_nhds_unique (hlim 0) (tendsto_const_nhds.congr' h0.symm)
    map_one' := tendsto_nhds_unique (hlim 1) (tendsto_const_nhds.congr' h1.symm)
    map_add' a b := tendsto_nhds_unique (hlim (a+b)) (((hlim a).add (hlim b)).congr' (hadd a b).symm)
    map_mul' a b := tendsto_nhds_unique (hlim (a*b)) (((hlim a).mul (hlim b)).congr' (hmul a b).symm) }
  exact ⟨χ,fun b => ⟨g b,hg b,he b,rfl⟩⟩

/-- Each reciprocal integral section extends through the actual cusp,
and its unique center value is a character of the actual reciprocal
normal order over exactly U=0. The field read remains the original
marked puncture, not another algebraic branch or a chosen local root. -/
theorem actual_marked_cusp_center
    (hp : p.Monic) (hf : IsField (AdjoinRoot (P N p))) :
    let F := K N p
    letI : Field F := (whole_isField N p hf).toField
    letI : Algebra ℂ[X] F := (polynomial F 0).toAlgebra
    ∃ (E : F →+* Germ0) (χ : InfinityOrder F →+* ℂ),
      Function.Injective E ∧
      (∀ z : OrdinaryRoot N p, E (intoWhole N p z) =
          Germ.ofFun (fun q => atCusp N hN c p hRoots t q z)) ∧
      χ.comp (algebraMap ℂ[X] (InfinityOrder F)) = Polynomial.evalRingHom 0 ∧
      Function.Surjective χ ∧
      ∀ b : InfinityOrder F, ∃ g : ℂ → ℂ,
        AnalyticAt ℂ g 0 ∧ E (algebraMap (InfinityOrder F) F b) = Germ.ofFun g ∧ g 0 = χ b := by
  let F := K N p
  letI : Field F := (whole_isField N p hf).toField
  letI : Algebra ℂ[X] F := (polynomial F 0).toAlgebra
  let B := InfinityOrder F
  obtain ⟨E,heInj,he,heFrac⟩ := actual_whole_cusp_germ N hN c p hRoots t hp hf
  let read : B →+* Germ0 := E.comp (algebraMap B F)
  have hCoeff := coefficients_at_reciprocal_chart N hN c p hRoots t hf E he
  have H (b : B) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ read b = Germ.ofFun g := by
    obtain ⟨f,hfE,hfA⟩ := heFrac (algebraMap B F b)
    have hI : IsIntegral ℂ[X] (algebraMap B F b) := b.property
    obtain ⟨P,hP,hPb⟩ := hI
    have heval := congrArg E hPb
    change E (P.eval₂ (algebraMap ℂ[X] F) (algebraMap B F b)) = E 0 at heval
    change E.comp (algebraMap ℂ[X] F) = polynomialGerm (cuspU N hN c) at hCoeff
    rw [Polynomial.hom_eval₂,hCoeff,hfE,map_zero] at heval
    have hmap :
        P.eval₂ (polynomialGerm (cuspU N hN c)) (Germ.ofFun f) =
          Germ.ofFun (fun q => P.eval₂ (Polynomial.evalRingHom (cuspU N hN c q)) (f q)) := by
      calc
        P.eval₂ (polynomialGerm (cuspU N hN c)) (Germ.ofFun f) =
            Germ.coeRingHom (𝓝[≠] (0 : ℂ))
              (P.eval₂ (funAlg (cuspU N hN c)) f) :=
          (Polynomial.hom_eval₂ P (funAlg (cuspU N hN c))
            (Germ.coeRingHom (𝓝[≠] (0 : ℂ))) f).symm
        _ = _ := by
          change Germ.ofFun (P.eval₂ (funAlg (cuspU N hN c)) f) = _
          apply congrArg (fun k : ℂ → ℂ => (Germ.ofFun k : Germ0))
          funext q
          let ev := Pi.evalRingHom (fun _ : ℂ => ℂ) q
          have h :
              ev.comp (funAlg (cuspU N hN c)) = Polynomial.evalRingHom (cuspU N hN c q) :=
            RingHom.ext (fun a => rfl)
          change ev (P.eval₂ (funAlg (cuspU N hN c)) f) = _
          exact (Polynomial.hom_eval₂ P (funAlg (cuspU N hN c)) ev f).trans
            (congrArg (fun m : ℂ[X] →+* ℂ => P.eval₂ m (f q)) h)
    rw [hmap] at heval
    have hroot : ∀ᶠ q in 𝓝[≠] (0 : ℂ),
        P.eval₂ (Polynomial.evalRingHom (cuspU N hN c q)) (f q) = 0 :=
      Germ.coe_eq.mp heval
    obtain ⟨g,hg,hgg⟩ := holomorphic_germ_of_bounded f hfA
      (eventually_bounded_monic_roots (cuspU N hN c) f
        (cuspU_holomorphic N hN c).continuousAt P hP hroot)
    exact ⟨g,hg,hfE.trans hgg⟩
  obtain ⟨χ,hχ⟩ := center_character_of_holomorphic_values read H
  have hχ0 : χ.comp (algebraMap ℂ[X] B) = Polynomial.evalRingHom 0 := by
    apply RingHom.ext
    intro a
    obtain ⟨g,hg,heq,hc⟩ := hχ (algebraMap ℂ[X] B a)
    have hβ : read (algebraMap ℂ[X] B a) = polynomialGerm (cuspU N hN c) a := by
      change E (algebraMap B F (algebraMap ℂ[X] B a)) = _
      rw [← IsScalarTower.algebraMap_apply ℂ[X] B F]
      exact RingHom.congr_fun hCoeff a
    have hEg : g =ᶠ[𝓝[≠] (0 : ℂ)] fun q => a.eval (cuspU N hN c q) :=
      Germ.coe_eq.mp (heq.symm.trans hβ)
    have ht : Tendsto (fun q => a.eval (cuspU N hN c q)) (𝓝[≠] (0 : ℂ))
        (𝓝 (a.eval 0)) := by
      have h₁ : ContinuousAt (fun u : ℂ => a.eval u) (cuspU N hN c 0) :=
        a.continuous.continuousAt
      have h₂ : ContinuousAt ((fun u : ℂ => a.eval u) ∘ cuspU N hN c) (0 : ℂ) :=
        h₁.comp (cuspU_holomorphic N hN c).continuousAt
      have h₃ : Tendsto ((fun u : ℂ => a.eval u) ∘ cuspU N hN c) (𝓝[≠] (0 : ℂ))
          (𝓝 (a.eval (cuspU N hN c 0))) := h₂.continuousWithinAt.tendsto
      simpa only [Function.comp_apply,cuspU_zero] using h₃
    exact hc.symm.trans (tendsto_nhds_unique
      (hg.continuousAt.continuousWithinAt.tendsto) (ht.congr' hEg.symm))
  refine ⟨E,χ,heInj,he,hχ0,?_,hχ⟩
  intro a
  exact ⟨algebraMap ℂ[X] B (C a),(RingHom.congr_fun hχ0 (C a)).trans Polynomial.eval_C⟩

end SelectedActualMarkedCuspCenterCharacter318

#print axioms SelectedActualMarkedCuspCenterCharacter318.actual_marked_cusp_center
