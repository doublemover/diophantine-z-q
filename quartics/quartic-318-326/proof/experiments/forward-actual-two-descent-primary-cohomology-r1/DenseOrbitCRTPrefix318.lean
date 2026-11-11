module
public import ActualMixedCRTPrefix318
public import RealOvalNormalization318
public section
noncomputable section

/-! Exact reduction of the remaining real input to density of the original
two-oval orbit. Density is explicitly a premise, not inferred here from the
separate algebraic or real elliptic integer-independence theorem. -/
namespace DenseOrbitCRTPrefix318
open Set TopologicalSpace
open ActualCyclicClosure318 ActualCyclicGuards318
open GeneratorScalarProgression318
open CoherentMultipleCharts318 (chartU)
open LocalGenerator318 (P)
set_option maxHeartbeats 2000000

instance pairConnected : ConnectedSpace Pair := by
  letI (e : Fin 2) : ConnectedSpace (RealQuarticGroup318.Oval (RealQuarticAmbient318.d e)) :=
    RealOvalNormalization318.oval_connected _
      (lt_trans zero_lt_one (RealQuarticAmbient318.d_gt_one e))
  infer_instance

lemma closure_connected (hdense : DenseRange pairOrbit) : ConnectedSpace cyclicClosure := by
  have he : (cyclicClosure : Set Pair)=univ := by
    rw [cyclicClosure_eq]
    exact hdense.closure_range
  apply Subtype.connectedSpace
  rw [he]
  exact isConnected_univ

lemma generator_good (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) :
    generatorInClosure∈ActualMixedCRTPrefix318.good labels (margin labels) := by
  change (1/(100*Real.sqrt 7):ℝ)< |scalarNorm generator| ∧
    ∀ j : Fin 4, margin labels j< |guard labels j generator|
  constructor
  · rw [scalarNorm_generator]
    have hs : 1<Real.sqrt (7:ℝ) := by
      have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤7)
      have hp := Real.sqrt_nonneg (7:ℝ)
      nlinarith
    have he : (1/(100*Real.sqrt 7):ℝ)<8/41 := by
      apply (div_lt_iff₀ (by positivity : (0:ℝ)<100*Real.sqrt 7)).mpr
      nlinarith
    simpa only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤8/41)] using he
  · intro j
    have hg := guard_generator_negative labels j (hn j)
    rw [abs_of_neg hg]
    unfold margin
    linarith

/-- The explicit P-centered region already has the exact scalar bound and
all fixed positive guard margins. If the original orbit is dense in the
whole pair, its closure is connected and this same point lies in G^0. -/
theorem concrete_component_inputs (hdense : DenseRange pairOrbit)
    (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) :
    (∀ j, 0<margin labels j) ∧
    (∃ X∈ActualMixedCRTPrefix318.good labels (margin labels),
      X∈connectedComponent (0:cyclicClosure)) ∧
    1 • (2 • generatorInClosure)∈connectedComponent (0:cyclicClosure) := by
  letI : ConnectedSpace cyclicClosure := closure_connected hdense
  refine ⟨margin_positive labels hn,⟨generatorInClosure,generator_good labels hn,?_⟩,?_⟩ <;>
    simp only [PreconnectedSpace.connectedComponent_eq_univ,Set.mem_univ]

/-- One remaining real hypothesis: density of the literal original pairOrbit.
All component and scalar/guard-region inputs are then constructed, with m=1,
before the original prime data. The same final h satisfies all three CRT
residues, original scalar bound, first51 rows and fixed signed roots. -/
theorem select_prefix_of_dense (hdense : DenseRange pairOrbit)
    (S q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (Pi Mminus Mplus L h₀ e B : ℕ)
    (hPi : 0<Pi) (hMm : 0<Mminus) (hMp : 0<Mplus) (hL : 0<L)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus) (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L=16) (hdivL : 64∣L) (hdivh₀ : 64∣h₀) :
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
      (h:ℤ) • P≠0 ∧ (1/(100*Real.sqrt 7):ℝ)< |(normCoefficient (chartU (h:ℤ)):ℝ)| ∧
      (∀ j : Fin 4, margin labels j< |(RealGuardTrace318.guardValue (labels j) ((h:ℤ) • P):ℝ)|) ∧
      CoherentMultiplePrefix318.witness q labels (h:ℤ) 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51)
        (CoherentMultiplePrefix318.witness q labels (h:ℤ)) ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
        (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) := by
  obtain ⟨hε,hmeets,hm⟩ := concrete_component_inputs hdense labels hn
  exact ActualMixedCRTPrefix318.select_prefix S q labels hn (margin labels) hε hmeets
    1 hm Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL
    (by simpa only [mul_one] using hdivL) (by simpa only [mul_one] using hdivh₀)

end DenseOrbitCRTPrefix318
