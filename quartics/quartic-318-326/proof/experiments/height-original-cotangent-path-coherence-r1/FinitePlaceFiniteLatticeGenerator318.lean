module
public import FinitePlacePrincipalLattice318
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Data.Finset.Max
public section
noncomputable section
namespace FinitePlaceFiniteLatticeGenerator318
open NumberField ActualFinitePlaceIntegers318 FinitePlacePrincipalLattice318
variable {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)
  (M : Submodule (Integers v) K) [Module.Finite (Integers v) M]

/-- A genuine finite nonzero embedded valuation-ring module has a
nonzero generator IN that module. Choose maximal norm in an actual
finite spanning set; no principal-image hypothesis is supplied. -/
theorem exists_generator (hM : M ≠ ⊥) :
    ∃ a : K, a ≠ 0 ∧ a ∈ M ∧ M = lattice v a := by
  classical
  obtain ⟨s,hs⟩ := (Submodule.FG.of_finite : M.FG)
  have hsne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [he,Finset.coe_empty,Submodule.span_empty] at hs
    exact hM hs.symm
  obtain ⟨a,ha,hmax⟩ := Finset.exists_max_image s (fun x : K => v x) hsne
  have ha0 : a ≠ 0 := by
    intro hz
    apply hM
    apply le_antisymm _ bot_le
    rw [←hs]
    apply Submodule.span_le.mpr
    intro x hx
    apply Submodule.mem_bot.mpr
    by_contra hx0
    have hh := hmax x hx
    rw [hz,map_zero] at hh
    exact (not_le_of_gt (v.pos hx0)) hh
  have ham : a ∈ M := by
    rw [←hs]
    exact Submodule.subset_span ha
  refine ⟨a,ha0,ham,le_antisymm ?_ (lattice_le_of_mem v a M ham)⟩
  rw [←hs]
  apply Submodule.span_le.mpr
  intro x hx
  apply (mem_iff_norm v a ha0 x).mpr
  have hh := (div_le_one (v.pos ha0)).mpr (hmax x hx)
  simpa only [div_eq_mul_inv] using hh

/-- An actual choice of a proved nonzero generator, not a free parameter. -/
@[expose] def generator (hM : M ≠ ⊥) : K := (exists_generator v M hM).choose
lemma generator_ne (hM : M ≠ ⊥) : generator v M hM ≠ 0 :=
  (exists_generator v M hM).choose_spec.1
lemma generator_mem (hM : M ≠ ⊥) : generator v M hM ∈ M :=
  (exists_generator v M hM).choose_spec.2.1
lemma generator_lattice (hM : M ≠ ⊥) : M = lattice v (generator v M hM) :=
  (exists_generator v M hM).choose_spec.2.2

/-- The radius does not depend on which proven generator is selected. -/
theorem generator_norm_unique (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (ea : M = lattice v a) (eb : M = lattice v b) : v a = v b := by
  have hba : b ∈ lattice v a := by
    rw [←ea,eb]
    exact ⟨1,by simp [generatorMap]⟩
  have hab : a ∈ lattice v b := by
    rw [←eb,ea]
    exact ⟨1,by simp [generatorMap]⟩
  have h1 := (mem_iff_norm v a ha b).mp hba
  have h2 := (mem_iff_norm v b hb a).mp hab
  apply le_antisymm
  · exact (div_le_one (v.pos hb)).mp (by simpa only [div_eq_mul_inv] using h2)
  · exact (div_le_one (v.pos ha)).mp (by simpa only [div_eq_mul_inv] using h1)
end FinitePlaceFiniteLatticeGenerator318
