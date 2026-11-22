module
public import ActualGaussianWeberIntegerModel318
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section

namespace ActualGaussianWeberIntegerGaloisGroup318

open NumberField
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberIntegerModel318

variable (L : Type*) [Field L] [hNF : NumberField L] [Algebra Base L]

include hNF in
/-- Finiteness of the actual Gaussian number-ring module, by restricting
its scalars to the standard integral lattice. -/
theorem gaussian_module_finite :
    letI := integralAlgebra (algebraMap Base L)
    Module.Finite GaussianInt (𝓞 L) := by
  letI := integralAlgebra (algebraMap Base L)
  letI : IsScalarTower ℤ GaussianInt (𝓞 L) := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    exact (map_intCast (algebraMap GaussianInt (𝓞 L)) z).symm
  exact Module.Finite.of_restrictScalars_finite ℤ GaussianInt (𝓞 L)

/-- The Gaussian action on the true ring of integers is torsion-free
and hence flat over the Dedekind domain of Gaussian integers. -/
theorem gaussian_module_flat :
    letI := integralAlgebra (algebraMap Base L)
    Module.Flat GaussianInt (𝓞 L) := by
  letI := integralAlgebra (algebraMap Base L)
  letI : Module.IsTorsionFree GaussianInt (𝓞 L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (integralEmbedding_injective (algebraMap Base L))
  infer_instance

variable [hGal : IsGalois Base L]

include hNF hGal in
/-- The stock Galois group is for the same Gaussian action on the
literal ring of integers as its arithmetic Frobenius action. -/
theorem gaussian_galois_group :
    letI := integralAlgebra (algebraMap Base L)
    IsGaloisGroup (L≃ₐ[Base]L) GaussianInt (𝓞 L) := by
  letI := integralAlgebra (algebraMap Base L)
  letI : Algebra GaussianInt L :=
    ((algebraMap Base L).comp (algebraMap GaussianInt Base)).toAlgebra
  letI : IsScalarTower GaussianInt Base L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower GaussianInt (𝓞 L) L :=
    IsScalarTower.of_algebraMap_eq (fun z => (integral_to_field (algebraMap Base L) z).symm)
  letI := integralExtension (algebraMap Base L)
  exact IsGaloisGroup.of_isFractionRing (L≃ₐ[Base]L) GaussianInt (𝓞 L) Base L

end ActualGaussianWeberIntegerGaloisGroup318
