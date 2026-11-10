module
public import ScalarSmallPrimeProgression318
public section
noncomputable section
namespace JointSmallPrimePreparation318
open SourceLocalProgression318 ScalarSmallPrimeProgression318
open SeventeenScalarCenter318 (center)
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A later admissible center may be chosen after the labels, preserving the
scalar neighborhood. The full detector neighborhood is then built there.
Both preparations hold on one final modulus, before any contact parameter or
later CRT index. Existence of that guard-avoiding center is not assumed away. -/
theorem join (a : ℤ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ L₀ : ℕ) (hL₀ : 0<L₀)
    (hscalar : ∀ h : ℕ, Nat.ModEq L₀ h h₀ → SmallPrepared a labels h)
    (h₁ : ℕ) (hcenter : Nat.ModEq L₀ h₁ h₀)
    (hzero : (h₁:ℤ)≠0) (hone : (h₁:ℤ)≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₁:ℤ))) :
    ∃ (L : ℕ) (N₂ N₃ N₁₇ : ℤ), 0<L ∧ L₀∣L ∧
      (∀ h : ℕ, Nat.ModEq L h h₁ → SmallPrepared a labels h) ∧
      Prepared 2 (a:ℚ) labels h₁ L N₂ 3 ∧
      Prepared 3 (a:ℚ) labels h₁ L N₃ 1 ∧
      Prepared 17 (a:ℚ) labels h₁ L N₁₇ 2 := by
  obtain ⟨L,N₂,N₃,N₁₇,hL,hdiv,h₂,h₃,h₁₇⟩ :=
    AllSmallPrimeProgression318.simultaneous (a:ℚ) labels hn h₁ L₀ hL₀ hzero hone hg
  refine ⟨L,N₂,N₃,N₁₇,hL,hdiv,?_,h₂,h₃,h₁₇⟩
  intro h hh
  exact hscalar h ((hh.of_dvd hdiv).trans hcenter)

/-- Full density of the literal pair orbit supplies the historically required
center adjustment inside any already prepared local residue class. -/
theorem adjust_center (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ L B : ℕ) (hL : 0<L) :
    ∃ h₁ : ℕ, B<h₁ ∧ 1<h₁ ∧ Nat.ModEq L h₁ h₀ ∧
      RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₁:ℤ)) ∧
      (1/100:ℝ)< |(GeneratorScalarProgression318.normCoefficient
        (CoherentMultipleCharts318.chartU (h₁:ℤ)):ℝ)| := by
  have hd : DenseRange (fun n : ℤ => n • ActualCyclicClosure318.generator) := by
    simpa only [ActualCyclicClosure318.pairOrbit_zsmul] using ActualPairDensity318.pairOrbit_dense
  have hm : ActualCyclicClosure318.generator-ActualCyclicClosure318.pairOrbit (h₀:ℤ)∈
      TopologicalSpace.connectedComponent (0:ActualCyclicClosure318.Pair) := by
    simp only [PreconnectedSpace.connectedComponent_eq_univ,Set.mem_univ]
  have hc : GeneratorScalarProgression318.Compatible h₀ L := by
    have he := MonotheticComponentSteps318.component_subset_stepClosure
      ActualCyclicClosure318.generator hd L hL hm
    simpa only [GeneratorScalarProgression318.Compatible,MonotheticComponentSteps318.stepClosure,
      natCast_zsmul] using he
  obtain ⟨t,ht,hregion⟩ := GeneratorScalarProgression318.tail_in_region labels hn h₀ L hc (max B 1)
  have hLt : t≤L*t := by nlinarith
  let h₁ := h₀+L*t
  have hbig : B<h₁ ∧ 1<h₁ := by dsimp [h₁]; omega
  have hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels (h₁:ℤ)) := by
    apply (CoherentMultiplePrefix318.guards_iff labels _).mpr
    intro j
    have he := hregion.2 j
    rw [ActualCyclicProgressions318.guard_value] at he
    have hp := GeneratorScalarProgression318.margin_positive labels hn j
    exact ne_of_lt (by exact_mod_cast (show (RealGuardTrace318.guardValue (labels j)
      ((h₁:ℤ) • LocalGenerator318.P):ℝ)<0 by dsimp [h₁]; linarith))
  refine ⟨h₁,hbig.1,hbig.2,MixedCRTComponentSelection318.progression_modEq L h₀ L t (dvd_refl _),hg,?_⟩
  simpa only [GeneratorScalarProgression318.scalarNorm_orbit] using hregion.1

/-- The center is now constructed after the labels while preserving the
actual scalar preparation. All local source thresholds and final modulus
are fixed before the later contact data and final common index. -/
theorem prepare_after_labels (a : ℤ) (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (h₀ L₀ B : ℕ) (hL₀ : 0<L₀)
    (hscalar : ∀ h : ℕ, Nat.ModEq L₀ h h₀ → SmallPrepared a labels h) :
    ∃ (h₁ L : ℕ) (N₂ N₃ N₁₇ : ℤ), B<h₁ ∧ 1<h₁ ∧
      Nat.ModEq L₀ h₁ h₀ ∧ 0<L ∧ L₀∣L ∧
      (∀ h : ℕ, Nat.ModEq L h h₁ → SmallPrepared a labels h) ∧
      Prepared 2 (a:ℚ) labels h₁ L N₂ 3 ∧
      Prepared 3 (a:ℚ) labels h₁ L N₃ 1 ∧
      Prepared 17 (a:ℚ) labels h₁ L N₁₇ 2 := by
  obtain ⟨h₁,hbig,hone,hcong,hguard,_⟩ := adjust_center labels hn h₀ L₀ B hL₀
  obtain ⟨L,N₂,N₃,N₁₇,hL,hdiv,hscalar',h₂,h₃,h₁₇⟩ :=
    join a labels hn h₀ L₀ hL₀ hscalar h₁ hcong
      (by exact_mod_cast (show h₁≠0 by omega))
      (by exact_mod_cast (show h₁≠1 by omega)) hguard
  exact ⟨h₁,L,N₂,N₃,N₁₇,hbig,hone,hcong,hL,hdiv,hscalar',h₂,h₃,h₁₇⟩

/-- End-to-end small-prime construction on the actual fixed integer/Lucas
labels. The common center, final modulus, and all three detector thresholds
are produced, not supplied by the caller. Remaining support primes outside
2,3,17 and global prime/rational-point inputs are separate obligations. -/
theorem integer_small_primes (a : ℤ) (A B N : ℕ) (hA : 6≤A) :
    ∃ e : ℕ, ∀ d : ℕ, ∀ hd : d≠0,
      let d' := PreparedAnchorLabels318.multiplier N (20*17^e*d)
      let hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _
        (mul_ne_zero (by positivity) hd)
      let labels := FixedArithmeticLabels318.labels a A B d' hd'
      ∀ M T : ℕ, 0<M → ∃ (h₁ L : ℕ) (N₂ N₃ N₁₇ : ℤ),
        T<h₁ ∧ 1<h₁ ∧ 0<L ∧ M∣L ∧ ScalarPreparedResidues318.modulus A B∣L ∧
        Nat.ModEq (ScalarPreparedResidues318.modulus A B) h₁ (ScalarPreparedResidues318.residue A B) ∧
        (∀ h : ℕ, Nat.ModEq L h h₁ → SmallPrepared a labels h) ∧
        Prepared 2 (a:ℚ) labels h₁ L N₂ 3 ∧
        Prepared 3 (a:ℚ) labels h₁ L N₃ 1 ∧
        Prepared 17 (a:ℚ) labels h₁ L N₁₇ 2 := by
  obtain ⟨e,he⟩ := ScalarSmallPrimeProgression318.prepare a A B N hA
  refine ⟨e,?_⟩
  intro d hd
  dsimp only
  let d' := PreparedAnchorLabels318.multiplier N (20*17^e*d)
  have hd' : d'≠0 := PreparedAnchorLabels318.multiplier_ne N _ (mul_ne_zero (by positivity) hd)
  let labels := FixedArithmeticLabels318.labels a A B d' hd'
  intro M T hM
  obtain ⟨L₀,hL₀,hM₀,hm₀,hscalar⟩ := he d hd M hM
  obtain ⟨h₁,L,N₂,N₃,N₁₇,hbig,hone,hcong,hL,hdiv,hscalar',h₂,h₃,h₁₇⟩ :=
    prepare_after_labels a labels (FixedArithmeticLabels318.labels_nonzero a A B d' hd')
      (center A B) L₀ T hL₀ hscalar
  refine ⟨h₁,L,N₂,N₃,N₁₇,hbig,hone,hL,hM₀.trans hdiv,hm₀.trans hdiv,?_,hscalar',h₂,h₃,h₁₇⟩
  exact (hcong.of_dvd hm₀).trans (SeventeenScalarCenter318.center_congruence A B)

end JointSmallPrimePreparation318
