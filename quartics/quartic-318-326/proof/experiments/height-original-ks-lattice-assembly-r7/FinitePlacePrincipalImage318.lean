module
public import FinitePlacePrincipalLattice318
public section
noncomputable section
namespace FinitePlacePrincipalImage318
open NumberField ActualFinitePlaceIntegers318 FinitePlacePrincipalLattice318
set_option maxHeartbeats 900000
variable {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)

/-- Equality of the actual embedded integral lattices detects the generator
norm, not merely the abstract rank-one isomorphism type. -/
theorem norm_eq_of_lattice_eq (α β : K) (hα : α≠0) (hβ : β≠0)
    (h : lattice v α=lattice v β) : v α=v β := by
  have hself (x : K) : x∈lattice v x :=
    (mem_iff v x x).mpr ⟨1,by simp⟩
  have hab : v α*(v β)⁻¹≤1 :=
    (mem_iff_norm v β hβ α).mp (h ▸ hself α)
  have hba : v β*(v α)⁻¹≤1 :=
    (mem_iff_norm v α hα β).mp (h.symm ▸ hself β)
  apply le_antisymm
  · have hx := (div_le_iff₀ (v.pos hβ)).mp
      (show v α/v β≤1 by simpa only [div_eq_mul_inv] using hab)
    simpa only [one_mul] using hx
  · have hx := (div_le_iff₀ (v.pos hα)).mp
      (show v β/v α≤1 by simpa only [div_eq_mul_inv] using hba)
    simpa only [one_mul] using hx

theorem lattice_eq_iff_norm (α β : K) (hα : α≠0) (hβ : β≠0) :
    lattice v α=lattice v β ↔ v α=v β :=
  ⟨norm_eq_of_lattice_eq v α β hα hβ,eq_of_norm v α β hα hβ⟩

/-- Multiplication by the literal scalar on the same generic frame. -/
@[expose] def scalarMap (k : K) : K →ₗ[Integers v] K where
  toFun x := k*x
  map_add' x y := mul_add k x y
  map_smul' a x := by simp only [Algebra.smul_def]; ring

/-- The image lattice is computed using the actual linear map, not a
redefinition of its norm or a choice of another rational frame. -/
theorem scalar_image (k α : K) :
    (lattice v α).map (scalarMap v k)=lattice v (k*α) := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨a,ha⟩ := (mem_iff v α y).mp hy
    apply (mem_iff v (k*α) x).mpr
    refine ⟨a,?_⟩
    change k*y=x at hxy
    rw [←hxy,←ha]
    ring
  · intro hx
    obtain ⟨a,ha⟩ := (mem_iff v (k*α) x).mp hx
    refine ⟨algebraMap (Integers v) K a*α,(mem_iff v α _).mpr ⟨a,rfl⟩,?_⟩
    change k*(algebraMap (Integers v) K a*α)=x
    rw [←ha]
    ring

/-- Integral span of actual products in two specified embedded lattices.
This is the multiplication image, and does not assert geometric provenance. -/
@[expose] def productLattice (α β : K) : Submodule (Integers v) K :=
  Submodule.span (Integers v) {z | ∃ x∈lattice v α, ∃ y∈lattice v β, x*y=z}

theorem product_lattice (α β : K) : productLattice v α β=lattice v (α*β) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    obtain ⟨a,rfl⟩ := (mem_iff v α x).mp hx
    obtain ⟨b,rfl⟩ := (mem_iff v β y).mp hy
    apply (mem_iff v (α*β) _).mpr
    refine ⟨a*b,?_⟩
    rw [map_mul]
    ring
  · apply lattice_le_of_mem
    apply Submodule.subset_span
    exact ⟨α,(mem_iff v α α).mpr ⟨1,by simp⟩,
      β,(mem_iff v β β).mpr ⟨1,by simp⟩,rfl⟩

/-- Exact local KS comparison. In particular k=210 is retained at its
nonunit places; no finite-place correction factor is discarded. -/
theorem norm_of_image_square (k α β : K) (hk : k≠0) (hα : α≠0) (hβ : β≠0)
    (h : (lattice v α).map (scalarMap v k)=productLattice v β β) :
    (v α)⁻¹/v k=((v β)⁻¹)^2 := by
  rw [scalar_image,product_lattice] at h
  have he := norm_eq_of_lattice_eq v (k*α) (β*β) (mul_ne_zero hk hα)
    (mul_ne_zero hβ hβ) h
  rw [map_mul,map_mul] at he
  calc
    (v α)⁻¹/v k=(v k*v α)⁻¹ := by simp [div_eq_mul_inv,mul_comm]
    _=(v β*v β)⁻¹ := congrArg Inv.inv he
    _=((v β)⁻¹)^2 := by simp [pow_two]
end FinitePlacePrincipalImage318
