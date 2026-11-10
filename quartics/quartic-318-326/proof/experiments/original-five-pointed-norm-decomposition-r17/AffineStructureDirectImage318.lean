module
public import AffineOpenSectionLifting318
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

public section
noncomputable section
namespace AffineStructureDirectImage318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AffineOpenSectionLifting318 SheafInverseImageConstants318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) [IsAffineHom f]

/-- Direct image preserves epimorphy for an extension whose kernel is the actual
structure sheaf on an integral source. No exactness on arbitrary additive sheaves is asserted. -/
theorem map_epi_of_structure_kernel (S : ShortComplex (ASheaf X))
    (hS : S.ShortExact) (e : S.X₁ ≅ StructureAdditiveSheaf318.sheaf X) :
    Epi ((directImage f.base).map S.g) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi (X:=Y.toTopCat)
    ((directImage f.base).map S.g)).mp
  constructor
  intro U t y hy
  obtain ⟨_,⟨V,hV,rfl⟩,hyV,hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  let i : V ⟶ U := homOfLE hVU
  obtain ⟨s,hs⟩ := surjective_affine_all S hS e (f ⁻¹ᵁ V) (hV.preimage f)
    (((directImage f.base).obj S.X₃).obj.map i.op t)
  exact ⟨V,i,⟨s,hs⟩,hyV⟩

/-- The actual injective-cokernel sequence used to compare H1 remains epimorphic after direct image. -/
theorem injective_cokernel_epi : Epi ((directImage f.base).map
    (cokernel.π (Injective.ι (StructureAdditiveSheaf318.sheaf X)))) := by
  let O := StructureAdditiveSheaf318.sheaf X
  let i := Injective.ι O
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
  exact map_epi_of_structure_kernel f S hS (Iso.refl _)

end AffineStructureDirectImage318
