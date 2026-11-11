module
public import RealDetectorSourceBridge318
public section
noncomputable section
namespace RealDetectorContinuity318
open ActualCyclicClosure318 RealQuarticAmbient318 RealDetectorRatios318 RealDetectorCoefficients318
open RealPadeSourceBridge318
open scoped Topology
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[fun_prop] lemma re_continuous : Continuous RealDetectorRatios318.re := by
  unfold RealDetectorRatios318.re
  fun_prop
@[fun_prop] lemma im_continuous : Continuous RealDetectorRatios318.im := by
  unfold RealDetectorRatios318.im
  fun_prop
@[fun_prop] lemma guard_continuous (labels : Fin 4 → ℤ) (j : Fin 4) :
    Continuous (RealDetectorCoefficients318.guard labels j) := by
  unfold RealDetectorCoefficients318.guard
  fun_prop

lemma root_continuousAt (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (X : Pair)
    (hd : (u labels (j.natAdd 4) e X)^2-(u labels (j.castAdd 4) e X)^2≠0) :
    ContinuousAt (RealDetectorCoefficients318.root labels j e) X := by
  unfold RealDetectorCoefficients318.root
  apply ContinuousAt.div <;> try fun_prop
  exact hd

/-- Continuity at an actual source orbit point is established only after
proving every reciprocal, Padé and root divisor nonzero at that same point. -/
theorem raw_continuousAt (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ)
    (h0 : h≠0) (h1 : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    ContinuousAt (raw q labels) (pairOrbit h) := by
  have dom := orbit_domains labels h h0 h1
  have hs : ∀ e, ContinuousAt (RealDetectorRatios318.shift e) (pairOrbit h) :=
    fun e => shift_continuousAt e _ (dom e).1
  have hf : ∀ e, ContinuousAt (RealDetectorRatios318.fV e) (pairOrbit h) :=
    fun e => fV_continuousAt e _ (dom e).1
  have ha : ∀ e, ContinuousAt (RealDetectorRatios318.argument e) (pairOrbit h) :=
    fun e => argument_continuousAt e _ (dom e).1
  have hc : ∀ e, ContinuousAt (RealDetectorRatios318.common e) (pairOrbit h) :=
    fun e => common_continuousAt e _ (dom e).1 (dom e).2.1 (dom e).2.2.1
  have hp : ∀ j e, ContinuousAt (primary labels j e) (pairOrbit h) :=
    fun j e => primary_continuousAt labels j e _ (dom e).1 ((dom e).2.2.2.2 j).1
  have hj : ∀ j e, ContinuousAt (alternatePolynomial labels j e) (pairOrbit h) :=
    fun j e => alternatePolynomial_continuousAt labels j e _ ((dom e).2.2.2.2 j).2
  have hr : ∀ j e, ContinuousAt (alternate labels j e) (pairOrbit h) :=
    fun j e => alternate_continuousAt labels j e _ (dom e).1 (dom e).2.1 (dom e).2.2.1
      ((dom e).2.2.2.2 j).2 (dom e).2.2.2.1
  have hpoly : ∀ e, ContinuousAt (fun X => Pade21Domains.PG (argument e X)/
      Pade21Domains.QG (argument e X)) (pairOrbit h) := by
    intro e
    apply ContinuousAt.div
    · unfold Pade21Domains.PG
      exact (continuousAt_const.sub (continuousAt_const.mul (ha e))).add
        (continuousAt_const.mul ((ha e).pow 2))
    · unfold Pade21Domains.QG
      exact continuousAt_const.sub (continuousAt_const.mul (ha e))
    · exact (dom e).2.2.1
  have hguards := (CoherentMultiplePrefix318.guards_iff labels h).mpr hg
  have hginv : ∀ j, ContinuousAt (fun X => (RealDetectorCoefficients318.guard labels j X)⁻¹)
      (pairOrbit h) := by
    intro j
    apply (guard_continuous labels j).continuousAt.inv₀
    rw [guard_orbit]
    exact_mod_cast hguards j
  have hroot : ∀ j e, ContinuousAt (RealDetectorCoefficients318.root labels j e) (pairOrbit h) := by
    intro j e
    apply root_continuousAt
    have hn := embedding_ne e (RealGuardWitness318.denominator_ne _ j (hguards j))
    simpa only [RealGuardWitness318.denominator,map_sub,map_pow,←u_orbit] using hn
  have hx : ∀ e : Fin 2, ContinuousAt (fun X : Pair => (X e).val.1) (pairOrbit h) :=
    fun e => (continuous_subtype_val.comp (continuous_apply e)).fst.continuousAt
  have hx2 : ContinuousAt (fun X : Pair => fun e : Fin 2 => (X e).val.1^2) (pairOrbit h) :=
    continuousAt_pi.mpr (fun e => (hx e).pow 2)
  have hx2s : ContinuousAt (fun X : Pair => fun e : Fin 2 => (X e).val.1^2*shift e X)
      (pairOrbit h) := continuousAt_pi.mpr (fun e => ((hx e).pow 2).mul (hs e))
  have hre2 := re_continuous.continuousAt.comp hx2
  have him2 := im_continuous.continuousAt.comp hx2
  have hre2s := re_continuous.continuousAt.comp hx2s
  have him2s := im_continuous.continuousAt.comp hx2s
  apply continuousAt_pi.mpr
  intro i
  unfold raw
  split <;> first
    | exact hre2
    | exact him2
    | exact hre2s
    | exact him2s
    | fun_prop (disch := aesop)

@[fun_prop] lemma fill_continuous : Continuous RealDetectorCoefficients318.fill := by
  apply continuous_pi
  intro i
  unfold RealDetectorCoefficients318.fill
  split <;> fun_prop

/-- The full real extension is continuous at every admissible original
coherent assignment, with no regularity assumed for arbitrary field inverses. -/
theorem coefficients_continuousAt (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ)
    (h0 : h≠0) (h1 : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    ContinuousAt (coefficients q labels) (pairOrbit h) := by
  apply continuousAt_pi.mpr
  intro i
  exact ((continuous_apply i.val).comp fill_continuous).continuousAt.comp
    (raw_continuousAt q labels h h0 h1 hg)

end RealDetectorContinuity318
