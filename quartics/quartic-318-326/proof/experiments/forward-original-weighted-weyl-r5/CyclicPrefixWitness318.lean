module
public import ActualCyclicProgressions318
public section
noncomputable section

/-! Literal first-51-row assignments on arbitrarily late compatible arithmetic
progressions. The remaining 237 source rows are not asserted here. -/
namespace CyclicPrefixWitness318
open LocalGenerator318 (P)
open CoherentMultiplePrefix318
open ActualCyclicProgressions318
set_option maxHeartbeats 2000000

/-- Each selected index gives one and the same assignment, original H point,
positive rational guards and historical signed roots. The input q is untouched. -/
theorem witness_in_progression (S q : ℚ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (r k : ℕ) (hk : 0<k) (hc : Compatible r k) (B : ℕ) :
    ∃ t : ℕ, B<r+k*t ∧
      let h : ℤ := ((r+k*t:ℕ):ℤ)
      h • P≠0 ∧ witness q labels h 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51) (witness q labels h) ∧
      (∀ j : Fin 4, margin labels j<(RealGuardTrace318.guardValue (labels j) (h • P):ℝ)) ∧
      (∀ j : Fin 4, RealGuardWitness318.root (u labels h) (v labels h) j=
        CoherentMultipleCharts318.fixedRoot (labels j)) := by
  obtain ⟨t,hbig,hbounds⟩ := guards_in_progression labels hn r k hk hc B
  have hh : ((r+k*t:ℕ):ℤ)≠0 := by
    exact_mod_cast (show r+k*t≠0 by omega)
  have hg : ∀ j : Fin 4,
      RealGuardTrace318.guardValue (labels j) (((r+k*t:ℕ):ℤ) • P)≠0 := by
    intro j
    have hp := lt_trans (margin_positive labels hn j) (hbounds j)
    exact ne_of_gt (by exact_mod_cast hp)
  refine ⟨t,hbig,RealMultiples318.multiple_P_nonzero _ hh,witness_input q labels _,
    witness_rows S q labels _ hh hg,hbounds,?_⟩
  intro j
  exact CoherentRootSign318.emitted_root_fixed labels _ j (hn j)
    (((guards_iff labels _).mpr hg) j)

/-- In particular, every positive modulus admits arbitrarily late literal
prefix witnesses with h divisible by that modulus. No guard assumptions remain. -/
theorem witness_at_multiples (S q : ℚ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (k : ℕ) (hk : 0<k) (B : ℕ) :
    ∃ t : ℕ, B<k*t ∧
      let h : ℤ := ((k*t:ℕ):ℤ)
      h • P≠0 ∧ witness q labels h 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51) (witness q labels h) ∧
      (∀ j : Fin 4, margin labels j<(RealGuardTrace318.guardValue (labels j) (h • P):ℝ)) ∧
      (∀ j : Fin 4, RealGuardWitness318.root (u labels h) (v labels h) j=
        CoherentMultipleCharts318.fixedRoot (labels j)) := by
  simpa only [zero_add] using
    witness_in_progression S q labels hn 0 k hk (compatible_zero k) B

/-- The same selected parameter retains every congruence whose modulus divides
k. This is congruence preservation, not construction of a permitted prime step. -/
theorem witness_with_residues (S q : ℚ) (labels : Fin 4 → ℤ)
    (hn : ∀ j, labels j≠0) (r k : ℕ) (hk : 0<k) (hc : Compatible r k) (B : ℕ) :
    ∃ t : ℕ, B<r+k*t ∧
      (∀ d : ℕ, d∣k → Nat.ModEq d (r+k*t) r) ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51)
        (witness q labels ((r+k*t:ℕ):ℤ)) := by
  obtain ⟨t,hbig,hP,hinput,hrows,hbounds,hroots⟩ :=
    witness_in_progression S q labels hn r k hk hc B
  exact ⟨t,hbig,fun d hd => CompactGuardProgression318.progression_modEq d r k t hd,hrows⟩

end CyclicPrefixWitness318
