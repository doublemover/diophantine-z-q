module
public import FinitePlaceFiniteLatticeGenerator318
public section
noncomputable section
namespace FinitePlaceMultiplicativeDual318
open NumberField ActualFinitePlaceIntegers318 FinitePlacePrincipalLattice318
variable {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)

@[expose] def multiply (a : K) : K →ₗ[Integers v] K where
  toFun x := a*x
  map_add' x y := mul_add a x y
  map_smul' r x := by
    simp only [Algebra.smul_def]
    ring

/-- The actual multiplicative integral dual inside the SAME point field.
It tests every element of the actual embedded lattice, not a chosen basis. -/
@[expose] def dual (M : Submodule (Integers v) K) : Submodule (Integers v) K :=
  ⨅ y : M, (lattice v 1).comap (multiply v y.val)

lemma mem_iff (M : Submodule (Integers v) K) (z : K) :
    z ∈ dual v M ↔ ∀ y ∈ M, y*z ∈ lattice v 1 := by
  simp only [dual,Submodule.mem_iInf,Submodule.mem_comap,multiply]
  exact ⟨fun h y hy => h ⟨y,hy⟩,fun h y => h y.val y.property⟩

lemma mem_unit_iff (z : K) : z ∈ lattice v (1:K) ↔ v z ≤ 1 := by
  rw [FinitePlacePrincipalLattice318.mem_iff_norm v 1 one_ne_zero]
  simp only [map_one,inv_one,mul_one]

/-- The full integral dual of a nonzero principal embedded lattice is
EXACTLY the inverse-generator lattice, not just an abstract isomorphism. -/
theorem dual_principal (a : K) (ha : a ≠ 0) :
    dual v (lattice v a) = lattice v a⁻¹ := by
  apply Submodule.ext
  intro z
  rw [mem_iff,FinitePlacePrincipalLattice318.mem_iff_norm v a⁻¹ (inv_ne_zero ha)]
  simp only [map_inv₀,inv_inv]
  constructor
  · intro hz
    have ham : a ∈ lattice v a := ⟨1,by
      change algebraMap (Integers v) K 1*a=a
      rw [map_one,one_mul]⟩
    have hh := (mem_unit_iff v (a*z)).mp (hz a ham)
    simpa only [map_mul,mul_comm] using hh
  · intro hz y hy
    obtain ⟨r,rfl⟩ := (FinitePlacePrincipalLattice318.mem_iff v a y).mp hy
    have haz : a*z ∈ lattice v (1:K) := by
      apply (mem_unit_iff v (a*z)).mpr
      simpa only [map_mul,mul_comm] using hz
    have hh := (lattice v (1:K)).smul_mem r haz
    simpa only [Algebra.smul_def,mul_assoc] using hh

/-- Bidual equality for the actual finite nonzero lattice, with no
perfect-pairing or reflexivity premise supplied by a caller. -/
theorem bidual (M : Submodule (Integers v) K) [Module.Finite (Integers v) M]
    (hM : M ≠ ⊥) : dual v (dual v M) = M := by
  obtain ⟨a,ha,_,he⟩ := FinitePlaceFiniteLatticeGenerator318.exists_generator v M hM
  rw [he,dual_principal v a ha,dual_principal v a⁻¹ (inv_ne_zero ha),inv_inv]

/-- The integral value is the literal field product, with membership
proved using the defining tests of the full embedded dual. -/
@[expose] def pairing (M : Submodule (Integers v) K) (z : dual v M) (y : M) : Integers v :=
  ⟨y.val*z.val,(bounded_iff v _).mp
    ((mem_unit_iff v _).mp ((mem_iff v M z.val).mp z.property y.val y.property))⟩
lemma pairing_value (M : Submodule (Integers v) K) (z : dual v M) (y : M) :
    algebraMap (Integers v) K (pairing v M z y)=y.val*z.val := rfl
end FinitePlaceMultiplicativeDual318
