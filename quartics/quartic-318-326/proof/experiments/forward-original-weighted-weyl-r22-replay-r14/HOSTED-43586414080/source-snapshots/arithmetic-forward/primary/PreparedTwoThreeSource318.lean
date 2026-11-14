module
public import ScalarPreparedCongruence318
public section
noncomputable section
namespace PreparedTwoThreeSource318
open Filter CircuitReplay Raw318FinalReplay GeneratorScalarProgression318
open PreparedIntegerSource318 TwoTwistPointRealization318 PreparedTwistSource318
open scoped Topology
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Genuine2/3 scalar preparation is now fixed before every real/contact/
prime choice, and is preserved by the literal continuity CRT congruence.
Only support primes other than2,3 retain local-depth producer premises. -/
theorem current_source_prepared_two_three (a : ℤ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (d : ℕ) (hd : d≠0)
    (hl : labels 1=ScalarPreparedCongruence318.scalarLabel d) :
    ∀ᶠ t : ℚ in atTop,
    ∀ (Pi Mminus Mplus L h₀ e B : ℕ),
      0<Pi → 0<Mminus → 0<Mplus → 0<L →
      Nat.Coprime Pi Mplus → Nat.Coprime Pi L →
      Nat.Coprime Mminus Mplus → Nat.Coprime Mplus L →
      Nat.gcd Mminus L=16 → 64∣L → 64∣h₀ → 384∣L → Nat.ModEq 384 h₀ 64 →
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
      (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)| ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
        (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) ∧
      let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) t
      (∀ j : Fin 3, 0<pre (190+51*j.val) ∧ pre (190+51*j.val)<17) ∧
      (0<scalarB (a:ℚ) labels (h:ℤ) ∧ scalarB (a:ℚ) labels (h:ℤ)<17) ∧
      (padicValRat 2 (ScalarForwardWitness318.W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0 ∧
       padicValRat 3 (ScalarForwardWitness318.W (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1))=0) ∧
      (IsSquare ((scalarB (a:ℚ) labels (h:ℤ):ℚ):ℚ_[2]) ∧
       IsSquare ((scalarB (a:ℚ) labels (h:ℤ):ℚ):ℚ_[3]) ∧
       IsSquare ((scalarB (a:ℚ) labels (h:ℤ):ℚ):ℚ_[17])) ∧
      (∀ (hprep : ∀ p : ℕ, p.Prime → p≠2 → p≠3 →
        0<padicValRat p (114444*ScalarForwardWitness318.inputR (a:ℚ)) →
        padicValRat p (ScalarForwardWitness318.inputR (a:ℚ))<padicValRat p ((DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) 37) ∧
        padicValRat p (ScalarForwardWitness318.inputR (a:ℚ))<padicValRat p (2*(DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) 33) ∧
        2*padicValRat p ((DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) 37)+29*padicValRat p (ScalarForwardWitness318.inputR (a:ℚ))<
          2*padicValRat p (ActualScalarRoot318.inverseNorm (labels 1))),
        IsSquare (scalarB (a:ℚ) labels (h:ℤ)).den ∧
        padicValRat 2 (scalarB (a:ℚ) labels (h:ℤ))=4 ∧
        padicValRat 3 (scalarB (a:ℚ) labels (h:ℤ))=2 ∧
        padicValRat 17 (scalarB (a:ℚ) labels (h:ℤ))=2) ∧
      (∀ P₀ : Realization (pre 190), ∀ P₁ : Realization (pre 241), ∀ P₂ : Realization (pre 292),
       ∀ P₃ : Realization (scalarB (a:ℚ) labels (h:ℤ)),
       ∀ A : ScalarCompleteSource318.Anchor (Current318FinalPolynomial.scale:ℚ) (FixedDetectorScales318.normProduct labels)
         (ActualScalarRoot318.inverseNorm (labels 1)), HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)) := by
  have hn1 : labels 1≠1 := by rw [hl]; exact (ScalarPreparedCongruence318.label_domains d hd).2.1
  filter_upwards [current_source_from_twists a labels hn hn1] with t ht
  intro Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀ h384 hmod₀
  obtain ⟨h,hbig,hA,hP,hL',hscalar,hroots,hbs,hscalarB,hsquares,hprep_old,hfinish⟩ :=
    ht Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀
  have hunits := ScalarPreparedCongruence318.continuity_preserves_units a labels d hd hl h L h₀ h384 hmod₀ hL'
  refine ⟨h,hbig,hA,hP,hL',hscalar,hroots,hbs,hscalarB,hunits,hsquares,?_,hfinish⟩
  intro hprep
  let w := DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)
  have hin : w 0=(a:ℚ) := DetectorGateWitness318.witness_input _ _ _
  have hW : ScalarForwardWitness318.W w (labels 1)≠0 := by
    intro hz
    have hb := hscalarB.1
    simp [scalarB,ScalarForwardWitness318.poleInput,ScalarForwardWitness318.quotient,hz] at hb
  have hH : w 37≠0 := by
    rw [ScalarActualInputs318.detector37]
    have he : (normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)≠0 :=
      abs_pos.mp (by linarith)
    exact_mod_cast he
  have hf : w 33≠0 := by
    rw [ScalarActualInputs318.detector33]
    apply ScalarPackedLocalUnit318.half_trace_ne
    simpa only [ScalarActualInputs318.detector37] using hH
  have hr : ScalarForwardWitness318.inputR (w 0)≠0 := by
    rw [hin]
    linarith [ScalarForwardWitness318.integer_inputR_large a]
  have hunit : ∀ p : ℕ, p.Prime →
      0<padicValRat p (114444*ScalarForwardWitness318.inputR (w 0)) →
      padicValRat p (ScalarForwardWitness318.W w (labels 1))=0 := by
    intro p hp hs
    by_cases hp2 : p=2
    · subst p
      exact hunits.1
    by_cases hp3 : p=3
    · subst p
      exact hunits.2
    letI : Fact p.Prime := ⟨hp⟩
    have hdepth := hprep p hp hp2 hp3 (by simpa only [hin] using hs)
    exact (ScalarPackedLocalUnit318.actual_unit p w (labels 1) hr hf hH (hn 1) hn1
      (by simpa only [hin] using hdepth.1)
      (by simpa only [hin] using hdepth.2.1)
      (by simpa only [hin] using hdepth.2.2)).2
  refine ⟨ScalarPolePreparation318.actual_square_denominator w (labels 1) a hin hW hunit,?_⟩
  have v17 := (ScalarSmallPrimePreparation318.actual_multiplier_values a).2.2
  rw [←hin] at v17
  exact ScalarSmallPrimePreparation318.actual_pole_thresholds w (labels 1) a hin hW
    hunits.1 hunits.2 (hunit 17 (by norm_num) (by omega))

end PreparedTwoThreeSource318
