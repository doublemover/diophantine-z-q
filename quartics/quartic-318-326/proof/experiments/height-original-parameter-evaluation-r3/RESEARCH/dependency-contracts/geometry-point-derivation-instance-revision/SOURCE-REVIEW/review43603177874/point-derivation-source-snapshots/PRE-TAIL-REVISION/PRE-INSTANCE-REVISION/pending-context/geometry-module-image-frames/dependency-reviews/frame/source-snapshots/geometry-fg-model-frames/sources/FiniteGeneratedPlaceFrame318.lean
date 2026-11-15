module
public import FinitePlacePrincipalImage318
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Module.Submodule.Equiv
public section
noncomputable section
namespace FiniteGeneratedPlaceFrame318
open NumberField ActualFinitePlaceIntegers318 FinitePlacePrincipalLattice318
variable {K : Type*} [Field K] [NumberField K] (w : FinitePlace K)

/-- A nonzero finitely generated embedded submodule over the ACTUAL finite
place integer ring is principal. The norm-membership criterion uses that ring's
fixed valuation normalization, not a completion or an arbitrary absolute value.
A generator is selected from a finite set augmented by the supplied nonzero member. -/
theorem exists_generator (M : Submodule (Integers w) K) (hfg : M.FG)
    (x : K) (hx : x∈M) (hne : x≠0) :
    ∃ γ : K, γ≠0 ∧ lattice w γ=M := by
  classical
  obtain ⟨s,hs⟩ := hfg
  obtain ⟨γ,hγ,hmax⟩ := (insert x s).exists_max_image (fun y : K => w y)
    ⟨x,Finset.mem_insert_self x s⟩
  have hpos : 0<w γ := lt_of_lt_of_le (w.pos hne)
    (hmax x (Finset.mem_insert_self x s))
  have hγne : γ≠0 := by
    intro hz
    simpa only [hz,map_zero,lt_self_iff_false] using hpos
  have hγM : γ∈M := by
    rcases Finset.mem_insert.mp hγ with rfl|hγs
    · exact hx
    · rw [←hs]
      exact Submodule.subset_span hγs
  refine ⟨γ,hγne,?_⟩
  apply le_antisymm
  · exact lattice_le_of_mem w γ M hγM
  · rw [←hs]
    apply Submodule.span_le.mpr
    intro y hy
    apply (mem_iff_norm w γ hγne y).mpr
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ hpos).mpr
    rw [one_mul]
    exact hmax y (Finset.mem_insert.mpr (Or.inr hy))

/-- Constructed scalar generator; no local frame is supplied as a premise. -/
@[expose] def generator (M : Submodule (Integers w) K) (hfg : M.FG)
    (x : K) (hx : x∈M) (hne : x≠0) : K :=
  Classical.choose (exists_generator w M hfg x hx hne)

theorem generator_ne (M : Submodule (Integers w) K) (hfg : M.FG)
    (x : K) (hx : x∈M) (hne : x≠0) : generator w M hfg x hx hne≠0 :=
  (Classical.choose_spec (exists_generator w M hfg x hx hne)).1

theorem lattice_generator (M : Submodule (Integers w) K) (hfg : M.FG)
    (x : K) (hx : x∈M) (hne : x≠0) : lattice w (generator w M hfg x hx hne)=M :=
  (Classical.choose_spec (exists_generator w M hfg x hx hne)).2

/-- Actual free frame of exactly the given model submodule, constructed from
finite generation and its nonzero section rather than assumed invertibility. -/
@[expose] def frame (M : Submodule (Integers w) K) (hfg : M.FG)
    (x : K) (hx : x∈M) (hne : x≠0) : Integers w ≃ₗ[Integers w] M :=
  (basis w _ (generator_ne w M hfg x hx hne)).trans
    (LinearEquiv.ofEq _ _ (lattice_generator w M hfg x hx hne))

theorem frame_value (M : Submodule (Integers w) K) (hfg : M.FG)
    (x : K) (hx : x∈M) (hne : x≠0) (a : Integers w) :
    (frame w M hfg x hx hne a : K)=algebraMap (Integers w) K a*generator w M hfg x hx hne := by
  simp only [frame,LinearEquiv.trans_apply,LinearEquiv.coe_ofEq_apply,basis_value]
end FiniteGeneratedPlaceFrame318
