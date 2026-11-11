module
public import ScalarLocalSquares318
public section
noncomputable section
namespace PreparedTwistSource318
open Filter CircuitReplay Raw318FinalReplay GeneratorScalarProgression318
open PreparedIntegerSource318 TwoTwistPointRealization318
open scoped Topology
set_option maxHeartbeats 0
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The exact final source consumer now takes rational points on the two
original twists and their literal squareclass maps. The scalar denominator
is proved square from actual unit preparation before those points are used.
The simultaneous point and local-unit producers remain explicit inputs. -/
theorem current_source_from_twists (a : ℤ) (labels : Fin 4 → ℤ)
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
      (IsSquare ((scalarB (a:ℚ) labels (h:ℤ):ℚ):ℚ_[2]) ∧
       IsSquare ((scalarB (a:ℚ) labels (h:ℤ):ℚ):ℚ_[3]) ∧
       IsSquare ((scalarB (a:ℚ) labels (h:ℤ):ℚ):ℚ_[17])) ∧
      (∀ (hprep : ∀ p : ℕ, p.Prime →
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
  filter_upwards [current_prepared_full_source a labels hn hn1] with t ht
  intro Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀
  obtain ⟨h,hbig,hA,hP,hL',hscalar,hroots,hbs,hscalarB,hfinish⟩ :=
    ht Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀
  refine ⟨h,hbig,hA,hP,hL',hscalar,hroots,hbs,hscalarB,?_,?_,?_⟩
  · exact ScalarLocalSquares318.actual_pole_squares _ _ a
      (DetectorGateWitness318.witness_input _ _ _)
  · intro hprep
    have hW : ScalarForwardWitness318.W
        (DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ)) (labels 1)≠0 := by
      intro hz
      have hb := hscalarB.1
      simp [scalarB,ScalarForwardWitness318.poleInput,ScalarForwardWitness318.quotient,hz] at hb
    have hH : DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ) 37≠0 := by
      rw [ScalarActualInputs318.detector37]
      have he : (normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)≠0 :=
        abs_pos.mp (by linarith)
      exact_mod_cast he
    have hf : DetectorGateWitness318.witness (a:ℚ) labels (h:ℤ) 33≠0 := by
      rw [ScalarActualInputs318.detector33]
      apply ScalarPackedLocalUnit318.half_trace_ne
      simpa only [ScalarActualInputs318.detector37] using hH
    apply ScalarSmallPrimePreparation318.actual_preparation _ _ a
      (DetectorGateWitness318.witness_input _ _ _) hf hH (hn 1) hn1 hW
    simpa only [DetectorGateWitness318.witness_input] using hprep

  · intro R₀ R₁ R₂ R₃ A
    exact hfinish R₀.pointPair R₁.pointPair R₂.pointPair R₃.pointPair A

end PreparedTwistSource318
