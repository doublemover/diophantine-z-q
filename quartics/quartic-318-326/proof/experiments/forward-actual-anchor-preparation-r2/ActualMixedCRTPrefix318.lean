module
public import MixedCRTComponentSelection318
public import GeneratorScalarProgression318
public section
noncomputable section

/-! The final mixed CRT residues, real component selection, original coherent
charts and literal source-prefix assignment are joined at one common index. -/
namespace ActualMixedCRTPrefix318
open Set TopologicalSpace
open ActualCyclicClosure318 ActualCyclicGuards318
open CoherentMultipleCharts318 (chartU)
open GeneratorScalarProgression318 (scalarNorm normCoefficient)
open LocalGenerator318 (P)
set_option maxHeartbeats 2000000

/-- The target uses the original two-embedding orbit and rational trace guards.
Positive margins are fixed before the prime-pattern and CRT data. -/
@[expose] def good (labels : Fin 4 → ℤ) (ε : Fin 4 → ℝ) : Set cyclicClosure :=
  {X | (1/(100*Real.sqrt 7):ℝ)< |scalarNorm X.val| ∧ ∀ j : Fin 4, ε j< |guard labels j X.val|}

lemma good_open (labels : Fin 4 → ℤ) (ε : Fin 4 → ℝ) : IsOpen (good labels ε) := by
  have he : good labels ε={X : cyclicClosure | (1/(100*Real.sqrt 7):ℝ)< |scalarNorm X.val|} ∩
      ⋂ j : Fin 4, {X : cyclicClosure | ε j< |guard labels j X.val|} := by
    ext X
    simp [good]
  rw [he]
  apply IsOpen.inter
  · exact isOpen_lt continuous_const
      (GeneratorScalarProgression318.scalarNorm_continuous.comp continuous_subtype_val).abs
  · exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const
      ((guard_continuous labels j).comp continuous_subtype_val).abs

/-- The actual final CRT progression supplies one h satisfying all three
residues, quantitative scalar/guard bounds, all first51 rows, and the fixed
historical signed roots. The existence of a good point in G^0 is still an
explicit premise, as is the concrete component return of the coherent orbit. -/
theorem select_prefix
    (S q : ℚ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (ε : Fin 4 → ℝ) (hε : ∀ j, 0<ε j)
    (hmeets : ∃ X∈good labels ε, X∈connectedComponent (0:cyclicClosure))
    (m : ℕ) (hm : m • (2 • generatorInClosure)∈connectedComponent (0:cyclicClosure))
    (Pi Mminus Mplus L h₀ e B : ℕ)
    (hPi : 0<Pi) (hMm : 0<Mminus) (hMp : 0<Mplus) (hL : 0<L)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus) (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L=16)
    (hmdivL : 64*m∣L) (hmdivh₀ : 64*m∣h₀) :
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ ∧
      (h:ℤ) • P≠0 ∧ (1/(100*Real.sqrt 7):ℝ)< |(normCoefficient (chartU (h:ℤ)):ℝ)| ∧
      (∀ j : Fin 4, ε j< |(RealGuardTrace318.guardValue (labels j) ((h:ℤ) • P):ℝ)|) ∧
      CoherentMultiplePrefix318.witness q labels (h:ℤ) 0=q ∧
      CircuitReplay.Constraints ((Raw318FinalReplay.stage0 S).take 51)
        (CoherentMultiplePrefix318.witness q labels (h:ℤ)) ∧
      (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
        (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) := by
  obtain ⟨h,hbig,hhA,hhP,hhL,hregion⟩ :=
    MixedCRTComponentSelection318.primary_depth_source64 generatorInClosure integer_orbit_dense
      m hm Pi Mminus Mplus L h₀ e B hPi hMm hMp hL hPm hPL hmp hpL hmL
      hmdivL hmdivh₀ (good labels ε) (good_open labels ε) hmeets
  have hh : (h:ℤ)≠0 := by exact_mod_cast (show h≠0 by omega)
  have hcoe : ((h • generatorInClosure : cyclicClosure) : Pair)=pairOrbit (h:ℤ) := by
    simpa only [natCast_zsmul] using coe_integer_multiple (h:ℤ)
  have hgood : (1/(100*Real.sqrt 7):ℝ)< |scalarNorm (pairOrbit (h:ℤ))| ∧
      ∀ j : Fin 4, ε j< |guard labels j (pairOrbit (h:ℤ))| := by
    simpa only [good,Set.mem_setOf_eq,hcoe] using hregion
  rw [GeneratorScalarProgression318.scalarNorm_orbit] at hgood
  have hbounds : ∀ j : Fin 4,
      ε j< |(RealGuardTrace318.guardValue (labels j) ((h:ℤ) • P):ℝ)| := by
    intro j
    simpa only [ActualCyclicProgressions318.guard_value] using hgood.2 j
  have hg : ∀ j : Fin 4, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • P)≠0 := by
    intro j
    have hp : (RealGuardTrace318.guardValue (labels j) ((h:ℤ) • P):ℝ)≠0 :=
      abs_pos.mp (lt_trans (hε j) (hbounds j))
    exact_mod_cast hp
  refine ⟨h,hbig,hhA,hhP,hhL,RealMultiples318.multiple_P_nonzero _ hh,hgood.1,hbounds,
    CoherentMultiplePrefix318.witness_input q labels _,
    CoherentMultiplePrefix318.witness_rows S q labels _ hh hg,?_⟩
  intro j
  exact CoherentRootSign318.emitted_root_fixed labels _ j (hn j)
    (((CoherentMultiplePrefix318.guards_iff labels _).mpr hg) j)

end ActualMixedCRTPrefix318
