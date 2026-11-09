module
public import DetectorGateWitness318
public import UnconditionalRealCRTPrefix318
public section
noncomputable section

/-! The same original CRT-selected index now fills the actual Padé/ratio
blocks and detector gates. This covers first107 of288 rows; the remaining181
and the production of the original prime-pattern data are still separate. -/
namespace Source107CRTWitness318
open GeneratorScalarProgression318
open CoherentMultipleCharts318 (chartU)
open LocalGenerator318 (P)

theorem select_prefix
    (S q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (Pi Mminus Mplus L h₀ e B : ℕ)
    (hPi : 0<Pi) (hMm : 0<Mminus) (hMp : 0<Mplus) (hL : 0<L)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus) (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L=16) (hdivL : 64∣L) (hdivh₀ : 64∣h₀) :
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
      (h:ℤ) • P≠0 ∧ (1/(100*Real.sqrt 7):ℝ)<|(normCoefficient (chartU (h:ℤ)):ℝ)| ∧
      (∀ j : Fin 4, margin labels j<|(RealGuardTrace318.guardValue (labels j) ((h:ℤ) • P):ℝ)|) ∧
      DetectorGateWitness318.witness q labels (h:ℤ) 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 107)
        (DetectorGateWitness318.witness q labels (h:ℤ)) ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
        (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) := by
  obtain ⟨h,hB,hr0,hr1,hrL,hpoint,hscalar,hguards,_hinput,_hrows,hroots⟩ :=
    UnconditionalRealCRTPrefix318.select_prefix S q labels hn Pi Mminus Mplus L h₀ e (B+1)
      hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀
  have hzero : (h:ℤ)≠0 := by
    intro hz
    have : h=0 := by exact_mod_cast hz
    omega
  have hone : (h:ℤ)≠1 := by
    intro hz
    have : h=1 := by exact_mod_cast hz
    omega
  have hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • P)≠0 := by
    intro j he
    have ht := hguards j
    have hp := GeneratorScalarProgression318.margin_positive labels hn j
    simp [he] at ht
    linarith
  exact ⟨h,by omega,hr0,hr1,hrL,hpoint,hscalar,hguards,
    DetectorGateWitness318.witness_input q labels (h:ℤ),
    DetectorGateWitness318.witness_first107 S q labels (h:ℤ) hzero hone hg,hroots⟩

end Source107CRTWitness318
