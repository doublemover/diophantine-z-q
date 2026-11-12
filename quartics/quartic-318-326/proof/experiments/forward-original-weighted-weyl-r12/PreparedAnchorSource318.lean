module
public import PhysicalAnchorFromHomogeneous318
public section
noncomputable section
namespace PreparedAnchorSource318
open Filter CircuitReplay Raw318FinalReplay GeneratorScalarProgression318
open PreparedIntegerSource318 TwoTwistPointRealization318 PreparedTwistSource318
open scoped Topology
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The actual fixed labels now also produce exceptional local physical-
anchor witnesses at the literal final scale. Only a rational homogeneous
zero remains for the anchor, with its affine domain proved rather than assumed. -/
theorem current_source_prepared_anchor (a : ℤ) (A₂ A₃ d : ℕ)
    (hdepth₂ : 6≤A₂) (hd : d≠0) :
    let labels := FixedArithmeticLabels318.labels a A₂ A₃
      (PreparedAnchorLabels318.multiplier (2^16) d)
      (PreparedAnchorLabels318.multiplier_ne (2^16) d hd)
    PhysicalAnchorFromHomogeneous318.CurrentLocalAnchors labels ∧
    (∀ j, 0<labels j ∧ Odd (labels j)) ∧
    (labels 0=3723*(2*a+1)^2 ∧
      (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
        (labels 1-2)^2*(labels 3)^2=1) ∧
    ∀ᶠ t : ℚ in atTop,
    ∀ (Pi Mminus Mplus L h₀ e B : ℕ),
      0<Pi → 0<Mminus → 0<Mplus → 0<L →
      Nat.Coprime Pi Mplus → Nat.Coprime Pi L →
      Nat.Coprime Mminus Mplus → Nat.Coprime Mplus L →
      Nat.gcd Mminus L=16 → 64∣L → 64∣h₀ → ScalarPreparedResidues318.modulus A₂ A₃∣L →
      Nat.ModEq (ScalarPreparedResidues318.modulus A₂ A₃) h₀ (ScalarPreparedResidues318.residue A₂ A₃) →
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
       ∀ H : PhysicalAnchorFromHomogeneous318.Homogeneous labels (2^16), HasSolution (stage0 (Current318FinalPolynomial.scale:ℚ)) (a:ℚ)) := by
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier (2^16) d
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne (2^16) d hd
  let labels := FixedArithmeticLabels318.labels a A₂ A₃ d' hd'
  obtain ⟨hlabels,hrelations,hevent⟩ :=
    PreparedLucasSource318.current_source_prepared_lucas a A₂ A₃ d' hdepth₂ hd'
  refine ⟨PhysicalAnchorFromHomogeneous318.actual_current_locals a A₂ A₃ d hd,
    hlabels,hrelations,?_⟩
  filter_upwards [hevent] with t ht
  intro Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀ hmodL hmod₀
  obtain ⟨h,hbig,hA,hP,hL',hscalar,hroots,hbs,hscalarB,hunits,hsquares,hprep,hfinish⟩ :=
    ht Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀ hmodL hmod₀
  refine ⟨h,hbig,hA,hP,hL',hscalar,hroots,hbs,hscalarB,hunits,hsquares,hprep,?_⟩
  intro P₀ P₁ P₂ P₃ H
  exact hfinish P₀ P₁ P₂ P₃ (PhysicalAnchorFromHomogeneous318.currentAnchor labels H)

end PreparedAnchorSource318
