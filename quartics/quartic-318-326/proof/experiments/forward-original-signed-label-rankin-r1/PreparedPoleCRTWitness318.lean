module
public import CompactDetectorRegion318
public section
noncomputable section
namespace PreparedPoleCRTWitness318
open Filter CircuitReplay Raw318FinalReplay PoleInputWitness318 ActualCyclicClosure318
open GeneratorScalarProgression318
open scoped Topology
set_option maxHeartbeats 0

/-- The analytic preparation now precedes every prime modulus and the final
CRT-selected index. All compact coefficient/access hypotheses are discharged
for the actual source assignment. Prime-pattern and simultaneous twist point
production remain arithmetic tasks; neither is inferred from this theorem. -/
theorem prepared_family (S q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) :
    ∀ᶠ t : ℚ in atTop,
    ∀ (Pi Mminus Mplus L h₀ e B : ℕ),
      0<Pi → 0<Mminus → 0<Mplus → 0<L →
      Nat.Coprime Pi Mplus → Nat.Coprime Pi L →
      Nat.Coprime Mminus Mplus → Nat.Coprime Mplus L →
      Nat.gcd Mminus L=16 → 64∣L → 64∣h₀ →
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
      (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)| ∧
      (∀ j : Fin 4, margin labels j<
        |(RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P):ℝ)|) ∧
      let w := fill (DetectorGateWitness318.witness q labels (h:ℤ)) t
      w 0=q ∧ Constraints ((stage0 S).take 152) w ∧ 0<w 190 ∧ w 190<17 ∧
      squareFactor (DetectorGateWitness318.witness q labels (h:ℤ)) t≠0 ∧
      w 190=ContactWeightWitness318.contact t*
        (squareFactor (DetectorGateWitness318.witness q labels (h:ℤ)) t)^2 ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
        (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) ∧
      (∀ P : NormalizedPolePoints318.PointPair (w 190),
        ∃ out : Assignment, out 0=q ∧ out 190=w 190 ∧
          Constraints ((stage0 S).take 157) out) := by
  obtain ⟨K,hK,U,hU,hne,hregion,hcoeff⟩ := CompactDetectorRegion318.exists_region q labels hn
  filter_upwards [UniformPoleFamilies318.uniform_actual_family S q labels K hK] with t ht
  intro Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀
  obtain ⟨h,hbig,hA,hP,hL',hU'⟩ := CompactDetectorRegion318.mixedCRT_access U hU hne
    Pi Mminus Mplus L h₀ e (B+1) hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀
  have h0 : (h:ℤ)≠0 := by omega
  have h1 : (h:ℤ)≠1 := by omega
  have hgood := hregion hU'
  have hguards : ∀ j : Fin 4,
      (RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P):ℝ)< -margin labels j := by
    intro j
    simpa only [ActualCyclicProgressions318.guard_value] using hgood.2 j
  have hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0 := by
    intro j
    have hp := margin_positive labels hn j
    exact_mod_cast (ne_of_lt (show (RealGuardTrace318.guardValue (labels j)
      ((h:ℤ) • LocalGenerator318.P):ℝ)<0 by linarith [hguards j]))
  have hK' : ContactChainReal318.project (DetectorGateWitness318.witness q labels (h:ℤ))∈K := by
    rw [←RealDetectorSourceBridge318.coefficients_orbit]
    exact hcoeff _ hU'
  obtain ⟨hin,hrows,hpos,hsmall,hs,hclass⟩ := ht (h:ℤ) h0 h1 hg hK'
  refine ⟨h,by omega,hA,hP,hL',?_,?_,hin,hrows,hpos,hsmall,hs,hclass,?_,?_⟩
  · simpa only [scalarNorm_orbit] using hgood.1
  · intro j
    have hp := margin_positive labels hn j
    rw [abs_of_neg (show (RealGuardTrace318.guardValue (labels j)
      ((h:ℤ) • LocalGenerator318.P):ℝ)<0 by linarith [hguards j])]
    linarith [hguards j]
  · intro j
    exact CoherentRootSign318.emitted_root_fixed labels (h:ℤ) j (hn j)
      (((CoherentMultiplePrefix318.guards_iff labels (h:ℤ)).mpr hg) j)
  · intro P
    let w := fill (DetectorGateWitness318.witness q labels (h:ℤ)) t
    let C := P.certificate (ne_of_gt hpos)
    refine ⟨PoleCertificateFill318.fill w C,?_,?_,?_⟩
    · exact (PoleCertificateFill318.fill_input w C).trans hin
    · simp [PoleCertificateFill318.fill]
    · exact PoleCertificateFill318.first157 S w C hrows

end PreparedPoleCRTWitness318
