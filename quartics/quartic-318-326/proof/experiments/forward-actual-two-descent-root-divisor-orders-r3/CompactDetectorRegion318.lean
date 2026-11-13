module
public import RealDetectorContinuity318
public section
noncomputable section
namespace CompactDetectorRegion318
open Set Filter TopologicalSpace ActualCyclicClosure318 GeneratorScalarProgression318
open RealDetectorCoefficients318 RealDetectorSourceBridge318
open scoped Topology
set_option maxHeartbeats 0

/-- A single nonempty original-orbit neighborhood has compactly bounded
actual stored coefficients and the original scalar/guard margins. It is
constructed before contact primes, their CRT moduli and the final index. -/
theorem exists_region (q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) :
    ∃ K : Set ContactChainReal318.Coeff, IsCompact K ∧
      ∃ U : Set Pair, IsOpen U ∧ U.Nonempty ∧ U⊆region labels ∧
        ∀ X∈U, coefficients q labels X∈K := by
  obtain ⟨t,ht,hregion⟩ := tail_in_region labels hn 1 1 (compatible_one 1) 2
  let h : ℤ := ((1+1*t:ℕ):ℤ)
  have h0 : h≠0 := by dsimp [h]; omega
  have h1 : h≠1 := by dsimp [h]; omega
  have hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0 := by
    intro j
    have hj := hregion.2 j
    rw [ActualCyclicProgressions318.guard_value] at hj
    have hp := margin_positive labels hn j
    change (RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P) : ℝ) <
      -margin labels j at hj
    have hneg : (RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P) : ℝ) < 0 := by
      linarith
    exact_mod_cast (ne_of_lt hneg)
  have hc := RealDetectorContinuity318.coefficients_continuousAt q labels h h0 h1 hg
  let c := coefficients q labels (pairOrbit h)
  have hball : (coefficients q labels) ⁻¹' Metric.ball c 1 ∈ 𝓝 (pairOrbit h) :=
    hc.preimage_mem_nhds (Metric.ball_mem_nhds c (by norm_num))
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hball
  refine ⟨Metric.closedBall c 1,isCompact_closedBall c 1,V∩region labels,
    hVo.inter (region_open labels),⟨pairOrbit h,hxV,hregion⟩,inter_subset_right,?_⟩
  intro X hX
  exact Metric.ball_subset_closedBall (hV hX.1)

/-- Full-density and connectedness turn that one fixed region into access
for every later original mixed-CRT data set. No new real-region hypothesis
is supplied after the arithmetic moduli are chosen. -/
theorem mixedCRT_access (U : Set Pair) (hU : IsOpen U) (hne : U.Nonempty)
    (Pi Mminus Mplus L h₀ e B : ℕ)
    (hPi : 0<Pi) (hMm : 0<Mminus) (hMp : 0<Mplus) (hL : 0<L)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus) (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L=16) (hdivL : 64∣L) (hdivh₀ : 64∣h₀) :
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧ pairOrbit (h:ℤ)∈U := by
  have hd : DenseRange (fun n : ℤ => n • generator) := by
    have he : pairOrbit = (fun n : ℤ => n • generator) := funext pairOrbit_zsmul
    rw [←he]
    exact ActualPairDensity318.pairOrbit_dense
  have hm : 1 • (2 • generator)∈connectedComponent (0:Pair) := by
    simp only [PreconnectedSpace.connectedComponent_eq_univ,mem_univ]
  have hmeets : ∃ X∈U, X∈connectedComponent (0:Pair) := by
    obtain ⟨X,hX⟩ := hne
    exact ⟨X,hX,by simp only [PreconnectedSpace.connectedComponent_eq_univ,mem_univ]⟩
  obtain ⟨h,hbig,hA,hP,hL',hregion⟩ :=
    MixedCRTComponentSelection318.primary_depth_source64 generator hd 1 hm
      Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL
      (by simpa using hdivL) (by simpa using hdivh₀) U hU hmeets
  refine ⟨h,hbig,hA,hP,hL',?_⟩
  simpa only [pairOrbit_zsmul,natCast_zsmul] using hregion

end CompactDetectorRegion318
