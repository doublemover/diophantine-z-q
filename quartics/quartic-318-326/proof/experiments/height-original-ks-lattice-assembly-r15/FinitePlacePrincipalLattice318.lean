module
public import OriginalGoodNormSupport318
public section
noncomputable section
namespace FinitePlacePrincipalLattice318
open NumberField ActualFinitePlaceIntegers318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)

/-- The integral multiples of a specified field-frame generator, with the
actual finite-place valuation-ring action. -/
@[expose] def generatorMap (α : K) : Integers v →ₗ[Integers v] K where
  toFun a := algebraMap (Integers v) K a*α
  map_add' a b := by rw [map_add,add_mul]
  map_smul' a b := by
    simp only [smul_eq_mul,map_mul,Algebra.smul_def]
    ring
@[expose] def lattice (α : K) : Submodule (Integers v) K := (generatorMap v α).range

theorem mem_iff (α x : K) : x∈lattice v α ↔
    ∃ a : Integers v, algebraMap (Integers v) K a*α=x := Iff.rfl

theorem generator_injective (α : K) (hα : α≠0) : Function.Injective (generatorMap v α) := by
  intro a b h
  apply Subtype.ext
  exact mul_right_cancel₀ hα h

/-- Exact norm membership in the genuine principal valuation-ring lattice.
The reverse direction constructs the actual integral coefficient x/α. -/
theorem mem_iff_norm (α : K) (hα : α≠0) (x : K) :
    x∈lattice v α ↔ v x*(v α)⁻¹≤1 := by
  rw [mem_iff]
  constructor
  · rintro ⟨a,rfl⟩
    have hp : v α≠0 := (v.pos hα).ne'
    rw [map_mul,mul_assoc,mul_inv_cancel₀ hp,mul_one]
    exact integer_bound v a
  · intro h
    have hx : v (x/α)≤1 := by simpa only [map_div₀,div_eq_mul_inv] using h
    refine ⟨⟨x/α,(bounded_iff v _).mp hx⟩,?_⟩
    change (x/α)*α=x
    exact div_mul_cancel₀ x hα

theorem lattice_le_of_mem (α : K) (M : Submodule (Integers v) K) (h : α∈M) :
    lattice v α≤M := by
  intro x hx
  obtain ⟨a,rfl⟩ := (mem_iff v α x).mp hx
  exact M.smul_mem a h

/-- Two actual principal lattices coincide when their frame generators have
the same norm. This does not identify the generators themselves. -/
theorem eq_of_norm (α β : K) (hα : α≠0) (hβ : β≠0) (h : v α=v β) :
    lattice v α=lattice v β := by
  apply Submodule.ext
  intro x
  rw [mem_iff_norm v α hα,mem_iff_norm v β hβ,h]

@[expose] def basisMap (α : K) : Integers v →ₗ[Integers v] lattice v α :=
  (generatorMap v α).rangeRestrict

theorem basisMap_bijective (α : K) (hα : α≠0) : Function.Bijective (basisMap v α) := by
  constructor
  · intro a b h
    apply generator_injective v α hα
    exact congrArg Subtype.val h
  · intro x
    obtain ⟨a,ha⟩ := x.property
    refine ⟨a,?_⟩
    apply Subtype.ext
    exact ha

/-- A constructed free rank-one frame of the actual embedded integral
lattice, not a rank premise added to the height consumer. -/
@[expose] def basis (α : K) (hα : α≠0) : Integers v ≃ₗ[Integers v] lattice v α :=
  LinearEquiv.ofBijective (basisMap v α) (basisMap_bijective v α hα)

theorem basis_value (α : K) (hα : α≠0) (a : Integers v) :
    (basis v α hα a:K)=algebraMap (Integers v) K a*α := rfl
end FinitePlacePrincipalLattice318
