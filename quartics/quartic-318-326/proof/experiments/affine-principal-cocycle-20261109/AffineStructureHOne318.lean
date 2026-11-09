module
public import AffineStructureSectionLifting318
public import SheafCohomologyRetraction318

public section
noncomputable section
namespace AffineStructureHOne318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Opposite TopologicalSpace
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [IsDomain R]

/-- Genuine Ext-defined H¹ of the original structure sheaf on Spec of a domain vanishes.
The proof passes through local lifts, original principal-open cocycles and original sheaf gluing. -/
theorem eq_zero (x : Sheaf.H (AffineStructureSectionLifting318.O (R:=R)) 1) : x = 0 := by
  let O := AffineStructureSectionLifting318.O (R:=R)
  let i := Injective.ι O
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i) }
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hS x
    (Ext.eq_zero_of_injective _) (n₀:=0) rfl
  obtain ⟨s,hs⟩ := AffineStructureSectionLifting318.surjective i S.g S.zero hS
    (Sheaf.H.equiv₀ S.X₃ isTerminalTop y)
  let z : Sheaf.H S.X₂ 0 := (Sheaf.H.equiv₀ S.X₂ isTerminalTop).symm s
  have hz : Sheaf.H.map S.g 0 z = y := by
    apply (Sheaf.H.equiv₀ S.X₃ isTerminalTop).injective
    rw [← Sheaf.H.equiv₀_naturality isTerminalTop S.g]
    simpa only [z,AddEquiv.apply_symm_apply] using hs
  rw [← hy,← hz,Sheaf.H.map_apply,Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass,Ext.comp_zero]

instance : Subsingleton (Sheaf.H (AffineStructureSectionLifting318.O (R:=R)) 1) :=
  subsingleton_of_forall_eq 0 (eq_zero R)

/-- The same theorem with the unchanged scheme-cohomology carrier used by the quotient packets. -/
theorem structureH_one_zero (x : SheafCohomologyRetraction318.structureH (Spec R) 1) : x = 0 :=
  eq_zero R x

end AffineStructureHOne318
