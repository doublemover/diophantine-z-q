module
public import ActualCyclicGuards318
public section
noncomputable section

/-! Recurrence in the actual step subgroup, with guard margins fixed before
choosing the step. This does not identify that subgroup with a real torus. -/
namespace ActualCyclicProgressions318
open Set Filter TopologicalSpace
open scoped Topology
open ActualCyclicClosure318 ActualCyclicGuards318
set_option maxHeartbeats 2000000

/-- The arithmetic progression can return to the identity precisely when its
negative translate belongs to the actual closed step subgroup. This is an
explicit topological input, not a claim of component density. -/
@[expose] def Compatible (r k : ℕ) : Prop :=
  -pairOrbit (r:ℤ) ∈
    (AddSubgroup.zmultiples ((k:ℤ) • generator)).topologicalClosure

lemma compatible_zero (k : ℕ) : Compatible 0 k := by
  unfold Compatible
  rw [pairOrbit_zsmul,zero_zsmul,neg_zero]
  exact AddSubgroup.zero_mem _

/-- A stronger elementary sufficient condition, useful before the component
comparison is available: every zero residue class modulo the step works. -/
lemma compatible_of_dvd (r k : ℕ) (hkr : k∣r) : Compatible r k := by
  obtain ⟨t,rfl⟩ := hkr
  unfold Compatible
  apply AddSubgroup.le_topologicalClosure
  change ∃ z : ℤ, z • ((k:ℤ) • generator)= -pairOrbit ((k*t:ℕ):ℤ)
  refine ⟨-(t:ℤ),?_⟩
  rw [pairOrbit_zsmul,←neg_zsmul,←mul_smul]
  congr 1
  push_cast
  ring

/-- These four strictly positive margins depend only on the fixed labels.
In particular they do not depend on the progression modulus or translate. -/
@[expose] def margin (labels : Fin 4 → ℤ) (j : Fin 4) : ℝ :=
  guard labels j 0/2

lemma margin_positive (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (j : Fin 4) :
    0<margin labels j := by
  exact half_pos (guard_zero_positive labels j (hn j))

@[expose] def region (labels : Fin 4 → ℤ) : Set Pair :=
  {X | ∀ j : Fin 4, margin labels j<guard labels j X}

lemma region_open (labels : Fin 4 → ℤ) : IsOpen (region labels) := by
  have he : region labels=⋂ j : Fin 4, {X : Pair | margin labels j<guard labels j X} := by
    ext X
    simp [region]
  rw [he]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const (guard_continuous labels j)

lemma zero_mem_region (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) :
    (0:Pair)∈region labels := by
  intro j
  have hp := guard_zero_positive labels j (hn j)
  dsimp [margin]
  linarith

lemma progression_point (r k t : ℕ) :
    pairOrbit (r:ℤ)+t • ((k:ℤ) • generator)=pairOrbit ((r+k*t:ℕ):ℤ) := by
  rw [pairOrbit_zsmul,pairOrbit_zsmul,←natCast_zsmul,←mul_smul,←add_zsmul]
  congr 1
  push_cast
  ring

/-- No surjectivity of multiplication on the full product is used. Compact
recurrence is applied to the actual step generator at the specified translate. -/
theorem tail_in_region (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (r k : ℕ) (hc : Compatible r k) (B : ℕ) :
    ∃ t : ℕ, B<t ∧ pairOrbit ((r+k*t:ℕ):ℤ)∈region labels := by
  have hrec := mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples.mpr hc
  have hnb : (fun X : Pair => pairOrbit (r:ℤ)+X) ⁻¹' region labels ∈
      𝓝 (-pairOrbit (r:ℤ)) :=
    ((region_open labels).preimage (continuous_const.add continuous_id)).mem_nhds
      (by simpa using zero_mem_region labels hn)
  obtain ⟨t,ht,hgood⟩ := frequently_atTop'.mp (hrec.frequently hnb) B
  refine ⟨t,ht,?_⟩
  rwa [←progression_point r k t]

lemma guard_value (labels : Fin 4 → ℤ) (j : Fin 4) (h : ℤ) :
    guard labels j (pairOrbit h)=
      (RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P):ℝ) := by
  rw [guard_pairOrbit,RealGuardAmbient318.guard_orbit]

/-- A quantitative guard bound on the same arithmetic point in the literal
source, with an arbitrarily late positive index in the prescribed progression. -/
theorem guards_in_progression (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (r k : ℕ) (hk : 0<k) (hc : Compatible r k) (B : ℕ) :
    ∃ t : ℕ, B<r+k*t ∧ ∀ j : Fin 4,
      margin labels j<
        (RealGuardTrace318.guardValue (labels j)
          (((r+k*t:ℕ):ℤ) • LocalGenerator318.P):ℝ) := by
  obtain ⟨t,ht,hgood⟩ := tail_in_region labels hn r k hc B
  have hkt : t≤k*t := by nlinarith
  refine ⟨t,by omega,?_⟩
  intro j
  have hj := hgood j
  rwa [guard_value] at hj

/-- Simultaneous positive guards exist beyond every bound in every positive
zero residue class, with the margins fixed before the step is specified. -/
theorem guards_at_multiples (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0)
    (k : ℕ) (hk : 0<k) (B : ℕ) :
    ∃ t : ℕ, B<k*t ∧ ∀ j : Fin 4,
      margin labels j<
        (RealGuardTrace318.guardValue (labels j)
          (((k*t:ℕ):ℤ) • LocalGenerator318.P):ℝ) := by
  simpa only [zero_add] using
    guards_in_progression labels hn 0 k hk (compatible_zero k) B

end ActualCyclicProgressions318
