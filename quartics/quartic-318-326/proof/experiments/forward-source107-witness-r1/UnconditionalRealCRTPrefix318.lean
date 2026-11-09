module
public import ActualPairDensity318
public import DenseOrbitCRTPrefix318
public section
noncomputable section

/-! The original mixed-CRT prefix theorem with all real-orbit, component-return
and scalar/guard-good intersection premises discharged. The original prime
moduli premises remain explicit, and the conclusion still covers first51
source rows rather than pretending to supply the remaining237. -/
namespace UnconditionalRealCRTPrefix318
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
      CoherentMultiplePrefix318.witness q labels (h:ℤ) 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51)
        (CoherentMultiplePrefix318.witness q labels (h:ℤ)) ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
        (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) := by
  exact DenseOrbitCRTPrefix318.select_prefix_of_dense ActualPairDensity318.pairOrbit_dense
    S q labels hn Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL hdivL hdivh₀

end UnconditionalRealCRTPrefix318
