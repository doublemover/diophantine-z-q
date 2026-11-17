module
public import ScalarCompleteSource318
public import Current318FinalPolynomial
public section
noncomputable section
namespace PreparedIntegerSource318
open Filter CircuitReplay Raw318FinalReplay GeneratorScalarProgression318 NormalizedPolePoints318
open scoped Topology
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def scalarB (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) : ℚ :=
  ScalarForwardWitness318.poleInput (DetectorGateWitness318.witness q labels h) (labels 1)

lemma scalar_domain (a : ℤ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (hn1 : labels 1≠1) (h : ℤ)
    (hscalar : (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU h):ℝ)|) :
    0<scalarB (a:ℚ) labels h ∧ scalarB (a:ℚ) labels h<17 := by
  have hb := ScalarActualInputs318.common_bounds h
  apply ScalarPoleRealDomain318.pole_domain
  · rw [DetectorGateWitness318.witness_input]
    exact ScalarForwardWitness318.integer_inputR_large a
  · rw [ScalarActualInputs318.detector33]
    exact hb.1
  · rw [ScalarActualInputs318.detector33]
    exact hb.2.1
  · rw [ScalarActualInputs318.detector37]
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_abs] using hscalar
  · rw [ScalarActualInputs318.detector37]
    exact hb.2.2
  · exact ActualScalarRoot318.inverseNorm_bound _ (hn 1) hn1

/-- Full source construction at the same previously selected h and t. The
four point pairs are actual rational points on the required two twists, and
Anchor is the explicit remaining ternary norm representation. No source gate
hypothesis beyond the already constructed248 nonpole equations is imported. -/
theorem complete_at_index (S : ℚ) (a : ℤ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (hn1 : labels 1≠1) (h : ℤ) (t : ℚ)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0)
    (hscalar : (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU h):ℝ)|)
    (hrows : Constraints (ThreeDetectorPrePole318.rows S)
      (ThreeDetectorUniformFamily318.witness (a:ℚ) labels h t))
    (hbs : ∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness (a:ℚ) labels h t (190+51*j.val))
    (P₀ : PointPair (ThreeDetectorUniformFamily318.witness (a:ℚ) labels h t 190))
    (P₁ : PointPair (ThreeDetectorUniformFamily318.witness (a:ℚ) labels h t 241))
    (P₂ : PointPair (ThreeDetectorUniformFamily318.witness (a:ℚ) labels h t 292))
    (P₃ : PointPair (scalarB (a:ℚ) labels h))
    (A : ScalarCompleteSource318.Anchor S (FixedDetectorScales318.normProduct labels)
      (ActualScalarRoot318.inverseNorm (labels 1))) : HasSolution (stage0 S) (a:ℚ) := by
  let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels h t
  let C₀ := P₀.certificate (ne_of_gt (hbs 0))
  let C₁ := P₁.certificate (ne_of_gt (hbs 1))
  let C₂ := P₂.certificate (ne_of_gt (hbs 2))
  let w := ThreePoleCertificates318.fill pre C₀ C₁ C₂
  have hw := ThreePoleCertificates318.first263 S pre C₀ C₁ C₂ hrows
  have hslot : ∀ i ∈ ([0,33,37,82,83,118,145] : List ℕ),
      w i = DetectorGateWitness318.witness (a:ℚ) labels h i := by
    simpa only [w,pre] using
      ScalarActualInputs318.preserved_slots (a:ℚ) labels h t C₀ C₁ C₂
  have hi : w 0=(a:ℚ) := (hslot 0 (by simp)).trans (DetectorGateWitness318.witness_input _ _ _)
  have hq : w 118=(w 0)^2 := by
    rw [hslot 118 (by simp),hi,ScalarActualInputs318.detector118]
  have hroot : ConcreteG8Domain.pair (w 82) (w 83)=CoherentMultipleCharts318.fixedRoot (labels 1) := by
    rw [hslot 82 (by simp),hslot 83 (by simp)]
    exact ScalarActualInputs318.detector_root _ labels hn h hg
  have hr : 10<ScalarForwardWitness318.inputR (w 0) := by
    rw [hi]
    exact ScalarForwardWitness318.integer_inputR_large a
  have hH : w 37≠0 := by
    rw [hslot 37 (by simp),ScalarActualInputs318.detector37]
    have he : (normCoefficient (CoherentMultipleCharts318.chartU h):ℝ)≠0 :=
      abs_pos.mp (by linarith)
    exact_mod_cast he
  have hbeq : ScalarForwardWitness318.poleInput w (labels 1)=scalarB (a:ℚ) labels h := by
    simp only [scalarB,ScalarForwardWitness318.poleInput,ScalarForwardWitness318.quotient,
      ScalarForwardWitness318.W,ScalarForwardWitness318.N,ScalarForwardWitness318.Q,
      hslot 0 (by simp),hslot 33 (by simp),hslot 37 (by simp)]
  have hb := scalar_domain a labels hn hn1 h hscalar
  have P₃' : PointPair (ScalarForwardWitness318.poleInput w (labels 1)) := by
    rw [hbeq]
    exact P₃
  have A' : ScalarCompleteSource318.Anchor S (w 145) (ActualScalarRoot318.inverseNorm (labels 1)) := by
    rw [hslot 145 (by simp),FixedDetectorScales318.actual_norm _ labels hn h hg]
    exact A
  have hout := ScalarCompleteSource318.hasSolution_of_point S w (labels 1) hw (hn 1) hn1 hq hroot
    (by linarith) hH (by linarith) (by rw [hbeq]; exact ne_of_gt hb.1) P₃' A'
  simpa only [hi] using hout

/-- The final source system, not a surrogate arithmetic predicate. All four
real pole ranges and all source gates are produced at one original CRT index.
The remaining rational-point and ternary-norm producers are stated explicitly. -/
theorem prepared_full_source (S : ℚ) (a : ℤ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (hn1 : labels 1≠1) :
    ∀ᶠ t : ℚ in atTop,
    ∀ (Pi Mminus Mplus L h₀ e B : ℕ),
      0<Pi → 0<Mminus → 0<Mplus → 0<L →
      Nat.Coprime Pi Mplus → Nat.Coprime Pi L →
      Nat.Coprime Mminus Mplus → Nat.Coprime Mplus L →
      Nat.gcd Mminus L=16 → 64∣L → 64∣h₀ →
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
      (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)| ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
        (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) ∧
      let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t
      (∀ j : Fin 3, 0<pre (190+51*j.val) ∧ pre (190+51*j.val)<17) ∧
      (0<scalarB (a:ℚ) labels (h:ℤ) ∧ scalarB (a:ℚ) labels (h:ℤ)<17) ∧
      (∀ P₀ : PointPair (pre 190), ∀ P₁ : PointPair (pre 241), ∀ P₂ : PointPair (pre 292),
       ∀ P₃ : PointPair (scalarB (a:ℚ) labels (h:ℤ)),
       ∀ A : ScalarCompleteSource318.Anchor S (FixedDetectorScales318.normProduct labels)
         (ActualScalarRoot318.inverseNorm (labels 1)), HasSolution (stage0 S) (a:ℚ)) := by
  filter_upwards [ThreeDetectorCRTWitness318.prepared_family S (a:ℚ) labels hn] with t ht
  intro Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀
  obtain ⟨h,hbig,hA,hP,hL',hscalar,hguards,hin,hrows,hbs,hroots,hfinish⟩ :=
    ht Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀
  refine ⟨h,hbig,hA,hP,hL',hscalar,hroots,hbs,scalar_domain a labels hn hn1 (h:ℤ) hscalar,?_⟩
  intro P₀ P₁ P₂ P₃ A
  have hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0 := by
    intro j
    have hp := margin_positive labels hn j
    have he := abs_pos.mp (lt_trans hp (hguards j))
    exact_mod_cast he
  exact complete_at_index S a labels hn hn1 (h:ℤ) t hg hscalar hrows (fun j => (hbs j).1) P₀ P₁ P₂ P₃ A

/-- Specialization to the exact retained final polynomial scale. -/
theorem current_prepared_full_source (a : ℤ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (hn1 : labels 1≠1) :
    ∀ᶠ t : ℚ in atTop,
    ∀ (Pi Mminus Mplus L h₀ e B : ℕ),
      0<Pi → 0<Mminus → 0<Mplus → 0<L →
      Nat.Coprime Pi Mplus → Nat.Coprime Pi L →
      Nat.Coprime Mminus Mplus → Nat.Coprime Mplus L →
      Nat.gcd Mminus L=16 → 64∣L → 64∣h₀ →
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
      (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)| ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
        (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) ∧
      let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t
      (∀ j : Fin 3, 0<pre (190+51*j.val) ∧ pre (190+51*j.val)<17) ∧
      (0<scalarB (a:ℚ) labels (h:ℤ) ∧ scalarB (a:ℚ) labels (h:ℤ)<17) ∧
      (∀ P₀ : PointPair (pre 190), ∀ P₁ : PointPair (pre 241), ∀ P₂ : PointPair (pre 292),
       ∀ P₃ : PointPair (scalarB (a:ℚ) labels (h:ℤ)),
       ∀ A : ScalarCompleteSource318.Anchor (Current318FinalPolynomial.scale:ℚ) (FixedDetectorScales318.normProduct labels)
         (ActualScalarRoot318.inverseNorm (labels 1)), HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)) :=
  prepared_full_source (Current318FinalPolynomial.scale:ℚ) a labels hn hn1

end PreparedIntegerSource318
