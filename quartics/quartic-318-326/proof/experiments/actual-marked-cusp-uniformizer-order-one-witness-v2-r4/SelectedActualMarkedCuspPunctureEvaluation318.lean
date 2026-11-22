module

public import SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
public import AllCuspJPole318
import Mathlib.Tactic.NormNum
import all SelectedActualWholeMarkedOrdinaryMeromorphicGerm318

public section
noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology MatrixGroups Polynomial
open GammaOneAtlas318
open FiniteCuspEnds318 WidthQParameter318
open SelectedComplexOrdinaryBase318
open SelectedActualComplexWholeRootField318 (Period periodMap)
open SelectedActualWholeMarkedOrdinaryMeromorphicGerm318
open OpenJComplexEvaluation318 (Admissible)

namespace SelectedActualMarkedCuspPunctureEvaluation318

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable (N : ℕ) [NeZero N] (hN : 5 ≤ N) (c : End N)

abbrev cuspInverse := RotatedPartialChart318.inverseFunction N hN (representative N c)

/-- A choice of lift of the actual original inverse cusp coordinate.
The value theorem below makes the marked evaluation independent of
this choice. At inadmissible values it remains an irrelevant totalization. -/
def originalCuspLift (q : ℂ) : UpperHalfPlane :=
  (quotient_surjective N (cuspInverse N hN c q)).choose

theorem originalCuspLift_projection (q : ℂ) :
    quotientMap N (originalCuspLift N hN c q) = cuspInverse N hN c q :=
  (quotient_surjective N (cuspInverse N hN c q)).choose_spec

private theorem j_eq_of_projection_eq {τ σ : UpperHalfPlane}
    (h : quotientMap N τ = quotientMap N σ) :
    ActualQJ318.jInvariant τ = ActualQJ318.jInvariant σ :=
  (QuotientJ318.jMap_projection N τ).symm.trans
    ((congrArg (QuotientJ318.jMap N) h).trans (QuotientJ318.jMap_projection N σ))

private theorem marked_eq_of_projection_eq {τ σ : UpperHalfPlane}
    (h : quotientMap N τ = quotientMap N σ) :
    SelectedMarkedPeriodCoordinate318.arithmeticX N τ =
      SelectedMarkedPeriodCoordinate318.arithmeticX N σ := by
  obtain ⟨g,hg,hT⟩ := (MarkedPeriod318.quotient_eq_iff_marked_transport N σ τ).mp h
  have hmem := (MarkedPeriod318.point_stabilizer N g σ).mp hT
  exact (congrArg (SelectedMarkedPeriodCoordinate318.arithmeticX N) hg).symm.trans
    (SelectedMarkedPeriodCoordinate318.arithmeticX_invariant N g hmem σ)

variable (p : (OpenJModel318.Base N)[X]) (hRoots : fullRootSet N p)
variable (t : Period)

private theorem ordinary_eval_eq_of_projection_eq {τ σ : Period}
    (h : quotientMap N τ.val = quotientMap N σ.val) :
    atPeriod N p hRoots τ = atPeriod N p hRoots σ := by
  have hJ : (periodMap N τ).1 = (periodMap N σ).1 :=
    Subtype.ext (j_eq_of_projection_eq N h)
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply,atPeriod_base,hJ]
  · exact (atPeriod_root N p hRoots τ).trans
      ((marked_eq_of_projection_eq N h).trans (atPeriod_root N p hRoots σ).symm)

/-- The exact original monic ordinary ring evaluated on the original
width coordinate, using the same marked root polynomial and full
root relation. -/
def atCusp (q : ℂ) : OrdinaryRoot N p →+* ℂ :=
  atDisk N p hRoots t (originalCuspLift N hN c q : ℂ)

theorem atCusp_of_ordinary_lift (q : ℂ) (τ : Period)
    (h : quotientMap N τ.val = cuspInverse N hN c q) :
    atCusp N hN c p hRoots t q = atPeriod N p hRoots τ := by
  let a := originalCuspLift N hN c q
  have hq : quotientMap N a = quotientMap N τ.val :=
    (originalCuspLift_projection N hN c q).trans h.symm
  have ha : Admissible a := by
    change ActualQJ318.jInvariant a ≠ 0 ∧ ActualQJ318.jInvariant a ≠ 1728
    rw [j_eq_of_projection_eq N hq]
    exact τ.property
  have hadm : Admissible (UpperHalfPlane.ofComplex (a : ℂ)) := by
    rw [UpperHalfPlane.ofComplex_apply]
    exact ha
  unfold atCusp
  change atDisk N p hRoots t (a : ℂ) = _
  rw [atDisk_of_admissible N p hRoots t (a : ℂ) hadm]
  apply ordinary_eval_eq_of_projection_eq N p hRoots
  change quotientMap N (UpperHalfPlane.ofComplex (a : ℂ)) = quotientMap N τ.val
  rw [UpperHalfPlane.ofComplex_apply]
  exact hq

/-- On the actual puncture, J reads the genuine width-w pole. -/
theorem literal_j_of_originalCuspLift (q : ℂ)
    (hq : q ∈ punctured (AllCuspOverlap318.width N hN c) 2) :
    ActualQJ318.jInvariant (originalCuspLift N hN c q) =
      AllCuspJPole318.localJ (AllCuspQJ318.natWidth N hN c) q := by
  rw [← QuotientJ318.jMap_projection N,originalCuspLift_projection]
  have hv : cuspInverse N hN c q = AllCuspOverlap318.oldMap N hN ⟨c,⟨q,hq⟩⟩ :=
    RotatedPartialChart318.inverseFunction_coe N hN (representative N c) ⟨q,hq⟩
  rw [hv]
  exact AllCuspQJ318.j_oldMap N hN c ⟨q,hq⟩

/-- A real punctured neighborhood of the actual cusp lies in the literal
ordinary opening: J escapes 0 and 1728 with the actual original width. -/
theorem eventually_ordinary_at_original_cusp :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), q ∈ punctured (AllCuspOverlap318.width N hN c) 2 ∧
      Admissible (originalCuspLift N hN c q) := by
  obtain ⟨δ,hδ,hlarge⟩ := AllCuspQJ318.small_parameter_large_j N hN c 1728
  have hDisc : ∀ᶠ q in 𝓝 (0 : ℂ), q ∈ AllCuspOverlap318.disc N hN c :=
    (AllCuspOverlap318.disc_open N hN c).mem_nhds
      (AllCuspFilling318.zeroPoint N hN c).property
  have hRadius : ∀ᶠ q in 𝓝 (0 : ℂ), ‖q‖ < δ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with q hq
    simpa only [Metric.mem_ball,dist_zero_right] using hq
  filter_upwards [hDisc.filter_mono nhdsWithin_le_nhds,
    hRadius.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hD hR hn
  have hq0 : q ≠ 0 := fun h => hn (Set.mem_singleton_iff.mpr h)
  have hq : q ∈ punctured (AllCuspOverlap318.width N hN c) 2 := ⟨hq0,hD⟩
  refine ⟨hq,?_⟩
  have hbig : (1728 : ℝ) < ‖ActualQJ318.jInvariant (originalCuspLift N hN c q)‖ := by
    rw [literal_j_of_originalCuspLift N hN c q hq]
    exact hlarge q hR hq0
  change ActualQJ318.jInvariant (originalCuspLift N hN c q) ≠ 0 ∧
    ActualQJ318.jInvariant (originalCuspLift N hN c q) ≠ 1728
  constructor <;> intro he
  · rw [he,norm_zero] at hbig
    norm_num at hbig
  · have hNrm : ‖(1728 : ℂ)‖ = (1728 : ℝ) := Complex.norm_natCast 1728
    rw [he,hNrm] at hbig
    exact (lt_irrefl _ hbig)

/-- Analyticity for every element of the actual original monic ring on
the punctured ordinary domain of the filled width chart. This uses a
local logarithm on that same chart, not analyticity at the cusp. -/
theorem original_cusp_ordinary_section_analytic
    (q : ℂ) (hq : q ∈ punctured (AllCuspOverlap318.width N hN c) 2)
    (ha : Admissible (originalCuspLift N hN c q)) (z : OrdinaryRoot N p) :
    AnalyticAt ℂ (fun v => atCusp N hN c p hRoots t v z) q := by
  let w := AllCuspOverlap318.width N hN c
  let g := representative N c
  let hw : 0 < w := AllCuspOverlap318.width_pos N hN c
  obtain ⟨τ,hτ⟩ := qMap_surjective w 2 hw (by norm_num) ⟨q,hq⟩
  have hqt : Function.Periodic.qParam w (τ.val : ℂ) = q := congrArg Subtype.val hτ
  have hpr : cuspInverse N hN c q = quotientMap N (g • τ.val) := by
    rw [← hqt]
    exact RotatedPartialChart318.inverseFunction_projection N hN g τ
  have hJ : ActualQJ318.jInvariant (g • τ.val) =
      ActualQJ318.jInvariant (originalCuspLift N hN c q) :=
    j_eq_of_projection_eq N (hpr.symm.trans (originalCuspLift_projection N hN c q).symm)
  have ha₀ : Admissible (g • τ.val) := by
    change ActualQJ318.jInvariant (g • τ.val) ≠ 0 ∧ ActualQJ318.jInvariant (g • τ.val) ≠ 1728
    rw [hJ]
    exact ha
  let a : Period := ⟨g • τ.val,ha₀⟩
  let r := WidthLocalInverse318.inverse w hw (τ.val : ℂ)
  have hr : AnalyticAt ℂ r q := by
    rw [← hqt]
    exact WidthLocalInverse318.inverse_analytic w hw (τ.val : ℂ)
  have hrq : r q = (τ.val : ℂ) := by
    rw [← hqt]
    exact WidthLocalInverse318.inverse_value w hw (τ.val : ℂ)
  let s := fun v : ℂ => (g • UpperHalfPlane.ofComplex (r v) : UpperHalfPlane)
  have hs : s q = a.val := by
    change g • UpperHalfPlane.ofComplex (r q) = g • τ.val
    rw [hrq,UpperHalfPlane.ofComplex_apply]
  let g₀ : GL (Fin 2) ℝ := g
  let gR : SL(2,ℝ) := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g
  have hg₀ : 0 < g₀.val.det := by
    change (0 : ℝ) < (↑gR : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [Matrix.SpecialLinearGroup.det_coe]
    exact zero_lt_one
  have hsA : AnalyticAt ℂ (fun v => (s v : ℂ)) q := by
    have hg : AnalyticAt ℂ (fun v => (g₀ • UpperHalfPlane.ofComplex v : UpperHalfPlane).coe) (r q) := by
      rw [hrq]
      exact UpperHalfPlane.analyticAt_smul hg₀ τ.val
    apply (hg.comp hr).congr
    exact Eventually.of_forall fun v =>
      (congrArg UpperHalfPlane.coe (ModularGroup.sl_moeb g (UpperHalfPlane.ofComplex (r v)))).symm
  let liftC : ℂ → ℂ := fun v => (s v : ℂ)
  let eval : ℂ → ℂ := fun v => atDisk N p hRoots a v z
  have hOld : AnalyticAt ℂ eval (liftC q) := by
    change AnalyticAt ℂ (fun v => atDisk N p hRoots a v z) (s q : ℂ)
    rw [hs]
    exact ordinary_ring_analytic N p (by omega) hRoots a z
  have hLift : AnalyticAt ℂ liftC q := hsA
  have hComp : AnalyticAt ℂ (eval ∘ liftC) q :=
    AnalyticAt.comp (g := eval) (f := liftC) hOld hLift
  apply hComp.congr
  have hHigh : ∀ᶠ v in 𝓝 q, (2 : ℝ) < (r v).im := by
    apply (Complex.continuous_im.continuousAt.comp hr.continuousAt).eventually
    exact isOpen_Ioi.mem_nhds (by
      change (2 : ℝ) < (r q).im
      rw [hrq]
      exact τ.property)
  have hInv : ∀ᶠ v in 𝓝 q, Function.Periodic.qParam w (r v) = v := by
    rw [← hqt]
    exact WidthLocalInverse318.inverse_right w hw (τ.val : ℂ)
  have hAdm : ∀ᶠ v in 𝓝 q, Admissible (UpperHalfPlane.ofComplex (s v : ℂ)) := by
    have H := OpenJLocalComparison318.admissible_eventually a.val a.property
    rw [← hs] at H
    exact hsA.continuousAt.eventually H
  filter_upwards [hHigh,hInv,hAdm] with v hv hi hadm
  have hvpos : 0 < (r v).im := lt_trans (by norm_num : (0 : ℝ) < 2) hv
  let b : UpperHalfPlane := ⟨r v,hvpos⟩
  let τv : high 2 := ⟨b,hv⟩
  have he : cuspInverse N hN c v = quotientMap N (s v) := by
    have H := RotatedPartialChart318.inverseFunction_projection N hN g τv
    change RotatedPartialChart318.inverseFunction N hN g (Function.Periodic.qParam w (r v)) =
      quotientMap N (g • b) at H
    have Hb : UpperHalfPlane.ofComplex (r v) = b :=
      UpperHalfPlane.ofComplex_apply_of_im_pos hvpos
    calc
      cuspInverse N hN c v = cuspInverse N hN c (Function.Periodic.qParam w (r v)) :=
        congrArg (cuspInverse N hN c) hi.symm
      _ = quotientMap N (g • b) := H
      _ = quotientMap N (s v) :=
        congrArg (fun u : UpperHalfPlane => quotientMap N (g • u)) Hb.symm
  have hp :
      quotientMap N (UpperHalfPlane.ofComplex (s v : ℂ)) = cuspInverse N hN c v := by
    rw [UpperHalfPlane.ofComplex_apply]
    exact he.symm
  have hf := atCusp_of_ordinary_lift N hN c p hRoots t v
    ⟨UpperHalfPlane.ofComplex (s v : ℂ),hadm⟩ hp
  change atDisk N p hRoots a (s v : ℂ) z = atCusp N hN c p hRoots t v z
  rw [atDisk_of_admissible N p hRoots a (s v : ℂ) hadm,hf]


/-- The entire original polynomial coefficient map, at the puncture of
this actual cusp, evaluates at the literal local width-w J function. -/
theorem original_cusp_polynomial_evaluation (a : ℂ[X]) :
    (fun q => atCusp N hN c p hRoots t q
      (AdjoinRoot.of (pC N p) (algebraMap ℂ[X] Base a))) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun q => a.eval (AllCuspJPole318.localJ (AllCuspQJ318.natWidth N hN c) q) := by
  filter_upwards [eventually_ordinary_at_original_cusp N hN c] with q hq
  let u : Period := ⟨originalCuspLift N hN c q,hq.2⟩
  rw [atCusp_of_ordinary_lift N hN c p hRoots t q u
      (originalCuspLift_projection N hN c q),atPeriod_base,evaluation_polynomial]
  change a.eval (ActualQJ318.jInvariant (originalCuspLift N hN c q)) = _
  rw [literal_j_of_originalCuspLift N hN c q hq.1]

end SelectedActualMarkedCuspPunctureEvaluation318

#print axioms SelectedActualMarkedCuspPunctureEvaluation318.atCusp_of_ordinary_lift
#print axioms SelectedActualMarkedCuspPunctureEvaluation318.eventually_ordinary_at_original_cusp
#print axioms SelectedActualMarkedCuspPunctureEvaluation318.original_cusp_ordinary_section_analytic
#print axioms SelectedActualMarkedCuspPunctureEvaluation318.original_cusp_polynomial_evaluation
