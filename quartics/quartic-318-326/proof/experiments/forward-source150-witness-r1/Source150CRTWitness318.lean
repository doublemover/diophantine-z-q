module
public import ContactChainWitness318
public import UnconditionalRealCRTPrefix318
public section
noncomputable section

/-! One common original CRT index and a free contact parameter fill first150
of288 source rows. The contact parameter is not frozen before its later prime
pattern use. Actual pole-realization and remaining138 rows remain separate. -/
namespace Source150CRTWitness318
open GeneratorScalarProgression318
open CoherentMultipleCharts318 (chartU)
open LocalGenerator318 (P)

theorem select_prefix
    (S q t : ℚ) (ht : t≠0) (hF : ContactWeightWitness318.contact t≠0)
    (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (Pi Mminus Mplus L h₀ e B : ℕ)
    (hPi : 0<Pi) (hMm : 0<Mminus) (hMp : 0<Mplus) (hL : 0<L)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus) (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L=16) (hdivL : 64∣L) (hdivh₀ : 64∣h₀) :
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
      (h:ℤ) • P≠0 ∧ (1/(100*Real.sqrt 7):ℝ)<|(normCoefficient (chartU (h:ℤ)):ℝ)| ∧
      (∀ j : Fin 4, margin labels j<|(RealGuardTrace318.guardValue (labels j) ((h:ℤ) • P):ℝ)|) ∧
      ContactChainWitness318.witness q labels (h:ℤ) t 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 150)
        (ContactChainWitness318.witness q labels (h:ℤ) t) ∧
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
    ContactChainWitness318.witness_input q labels (h:ℤ) t,
    ContactChainWitness318.witness_first150 S q labels (h:ℤ) t hzero hone ht hF hg,hroots⟩

end Source150CRTWitness318
