module
public import FinitePlacePrincipalImage318
public section
noncomputable section
namespace EmbeddedLatticeFrames318
open NumberField ActualFinitePlaceIntegers318 FinitePlacePrincipalLattice318
open FinitePlacePrincipalImage318
variable {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)

/-- Extract a generator from a supplied free frame of a specified embedded
model lattice. Neither the lattice nor its geometric origin is constructed here. -/
@[expose] def frameGenerator {M : Submodule (Integers v) K}
    (e : Integers v ≃ₗ[Integers v] M) : K := (e 1 : K)

theorem frame_value {M : Submodule (Integers v) K}
    (e : Integers v ≃ₗ[Integers v] M) (a : Integers v) :
    (e a : K)=algebraMap (Integers v) K a*frameGenerator v e := by
  have h := congrArg (fun z : M => (z : K)) (e.map_smul a (1 : Integers v))
  simpa [frameGenerator, Algebra.smul_def] using h

theorem frameGenerator_ne {M : Submodule (Integers v) K}
    (e : Integers v ≃ₗ[Integers v] M) : frameGenerator v e≠0 := by
  intro h
  have he : e 1=e 0 := by
    apply Subtype.ext
    simpa only [frameGenerator, map_zero, Submodule.coe_zero] using h
  exact one_ne_zero (e.injective he)

/-- The principal lattice is the exact supplied submodule, not an abstractly
isomorphic replacement and not a lattice manufactured from a desired norm. -/
theorem lattice_frameGenerator {M : Submodule (Integers v) K}
    (e : Integers v ≃ₗ[Integers v] M) : lattice v (frameGenerator v e)=M := by
  apply le_antisymm
  · exact lattice_le_of_mem v _ M (e 1).property
  · intro x hx
    obtain ⟨a,ha⟩ := e.surjective ⟨x,hx⟩
    apply (mem_iff v _ x).mpr
    refine ⟨a,?_⟩
    rw [←frame_value v e a]
    exact congrArg (fun z : M => (z : K)) ha

/-- Free-frame choice does not change the finite norm of the specified lattice. -/
theorem frameGenerator_norm_eq {M : Submodule (Integers v) K}
    (e f : Integers v ≃ₗ[Integers v] M) :
    v (frameGenerator v e)=v (frameGenerator v f) := by
  apply norm_eq_of_lattice_eq v _ _ (frameGenerator_ne v e) (frameGenerator_ne v f)
  rw [lattice_frameGenerator, lattice_frameGenerator]

/-- A supplied surjective map between actual embedded lattices, with its
literal generic scalar formula, determines the image in the same ambient field.
The map and its generic normalization remain inputs; no image equality is assumed. -/
theorem scalar_image_of_surjective {M N : Submodule (Integers v) K}
    (f : M →ₗ[Integers v] N) (hf : Function.Surjective f) (k : K)
    (hscalar : ∀ x : M, (f x : K)=k*(x : K)) :
    M.map (scalarMap v k)=N := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨y,hy,hxy⟩
    have he : (f ⟨y,hy⟩ : K)=x := (hscalar ⟨y,hy⟩).trans hxy
    exact he ▸ (f ⟨y,hy⟩).property
  · intro hx
    obtain ⟨y,hy⟩ := hf ⟨x,hx⟩
    refine ⟨(y : K),y.property,?_⟩
    change k*(y : K)=x
    exact (hscalar y).symm.trans (congrArg (fun z : N => (z : K)) hy)

/-- An invertible comparison with the required normalization supplies the
surjectivity used above. It is stronger data than a numerical norm equality. -/
theorem scalar_image_of_equiv {M N : Submodule (Integers v) K}
    (e : M ≃ₗ[Integers v] N) (k : K)
    (hscalar : ∀ x : M, (e x : K)=k*(x : K)) :
    M.map (scalarMap v k)=N :=
  scalar_image_of_surjective v e.toLinearMap e.surjective k hscalar
end EmbeddedLatticeFrames318
