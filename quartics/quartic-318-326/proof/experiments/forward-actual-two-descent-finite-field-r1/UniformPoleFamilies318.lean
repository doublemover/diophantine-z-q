module
public import PoleCertificateFill318
public section
noncomputable section
namespace UniformPoleFamilies318
open Filter CircuitReplay Raw318FinalReplay PoleInputWitness318 ContactChainReal318

/-- The threshold is chosen before h. Every later original coherent orbit
assignment in K has all first152 rows, the required real pole range and the
exact contact squareclass. Producing such a compact K with arithmetic access
is a distinct remaining construction, not a premise hidden in continuity. -/
theorem uniform_actual_family (S q : ℚ) (labels : Fin 4 → ℤ)
    (K : Set Coeff) (hK : IsCompact K) :
    ∀ᶠ t : ℚ in atTop, ∀ h : ℤ, h≠0 → h≠1 →
      (∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) →
      project (DetectorGateWitness318.witness q labels h)∈K →
      let w := fill (DetectorGateWitness318.witness q labels h) t
      w 0=q ∧ Constraints ((stage0 S).take 152) w ∧
      0<w 190 ∧ w 190<17 ∧
      squareFactor (DetectorGateWitness318.witness q labels h) t≠0 ∧
      w 190=ContactWeightWitness318.contact t*
        (squareFactor (DetectorGateWitness318.witness q labels h) t)^2 := by
  filter_upwards [UniformPoleDomain318.uniform_pole_domain K hK] with t ht
  intro h hzero hone hg hwK
  obtain ⟨ht2,hall⟩ := ht
  obtain ⟨hr,hpos,hsmall⟩ := hall _ hwK
  have ht0 : t≠0 := by linarith
  have ht1 : t≠1 := by linarith
  have hF := (ContactChainLimits318.contact_positive t ht2).ne'
  refine ⟨?_,?_,?_,?_,squareFactor_ne _ t hr ht1,?_⟩
  · rw [fill_input,DetectorGateWitness318.witness_input]
  · exact PoleInputFamily318.first152 S _ t ht1 hF hr
      (ContactChainWitness318.witness_first150 S q labels h t hzero hone ht0 hF hg)
  · simpa [fill] using hpos
  · simpa [fill] using hsmall
  · simpa [fill] using pole_squareclass (DetectorGateWitness318.witness q labels h) t

/-- At the same uniform threshold, actual normalized twist points complete
the first pole block. All point, source, contact and orbit data refer to the
same b; no independent choice of a convenient pole parameter is allowed. -/
theorem uniform_first157 (S q : ℚ) (labels : Fin 4 → ℤ)
    (K : Set Coeff) (hK : IsCompact K) :
    ∀ᶠ t : ℚ in atTop, ∀ h : ℤ, h≠0 → h≠1 →
      (∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) →
      project (DetectorGateWitness318.witness q labels h)∈K →
      let w := fill (DetectorGateWitness318.witness q labels h) t
      ∀ P : NormalizedPolePoints318.PointPair (w 190),
      ∃ out : Assignment, out 0=q ∧ out 190=w 190 ∧
        Constraints ((stage0 S).take 157) out := by
  filter_upwards [uniform_actual_family S q labels K hK] with t ht
  intro h hzero hone hg hK'
  dsimp only
  intro P
  obtain ⟨hinput,hrows,hpos,hsmall,hs,hclass⟩ := ht h hzero hone hg hK'
  let w := fill (DetectorGateWitness318.witness q labels h) t
  let C := P.certificate (ne_of_gt hpos)
  refine ⟨PoleCertificateFill318.fill w C,?_,?_,?_⟩
  · exact (PoleCertificateFill318.fill_input w C).trans hinput
  · simp [PoleCertificateFill318.fill,w]
  · exact PoleCertificateFill318.first157 S w C hrows

end UniformPoleFamilies318
