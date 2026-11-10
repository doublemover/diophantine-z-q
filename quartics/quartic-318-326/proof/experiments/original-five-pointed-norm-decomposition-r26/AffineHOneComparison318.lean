module
public import AffineStructureDirectImage318
public import AdjunctionExtOneSurjection318
public import SchemeSourceCohomology318

public section
noncomputable section
namespace AffineHOneComparison318
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open SheafInverseImageConstants318 SheafCohomologyRetraction318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) [IsAffineHom f]

/-- Surjectivity of the unchanged canonical comparison for an affine map from an integral source. -/
theorem comparison_surjective : Function.Surjective (SchemeSourceCohomology318.comparison f 1) := by
  have hs := AdjunctionExtOneSurjection318.mate_one_surjective
    (adjunction f.base) (integerSheaf Y.toTopCat) (StructureAdditiveSheaf318.sheaf X)
    (AffineStructureDirectImage318.injective_cokernel_epi f)
  intro x
  obtain ⟨z,hz⟩ := hs ((Ext.mk₀ (integerIso f.base).hom).comp x (zero_add 1))
  refine ⟨z,?_⟩
  change (Ext.mk₀ (integerIso f.base).inv).comp
    (AdjunctionExtOneInjection318.mate (adjunction f.base) _ _ 1 z) (zero_add 1) = x
  calc
    _ = (Ext.mk₀ (integerIso f.base).inv).comp
        ((Ext.mk₀ (integerIso f.base).hom).comp x (zero_add 1)) (zero_add 1) :=
      congrArg (fun q => (Ext.mk₀ (integerIso f.base).inv).comp q (zero_add 1)) hz
    _ = x := by
      rw [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,
        Iso.inv_hom_id,Ext.mk₀_id_comp]

theorem comparison_bijective : Function.Bijective (SchemeSourceCohomology318.comparison f 1) :=
  ⟨SchemeSourceCohomology318.comparison_one_injective f,comparison_surjective f⟩

/-- The additive equivalence has the exact canonical comparison as its forward map. -/
@[expose] def equivalence : pushedH f 1 ≃+ structureH X 1 :=
  AddEquiv.ofBijective (SchemeSourceCohomology318.comparison f 1) (comparison_bijective f)

theorem equivalence_apply (x : pushedH f 1) :
    equivalence f x = SchemeSourceCohomology318.comparison f 1 x := rfl

/-- The original sheaf trace now transfers genuine source H1 via the inverse comparison. -/
@[expose] def transfer (r : StructureAdditiveSheaf318.pushed f ⟶ StructureAdditiveSheaf318.sheaf Y) :
    structureH X 1 →+ structureH Y 1 :=
  (SheafCohomologyRetraction318.transfer f r 1).comp (equivalence f).symm.toAddMonoidHom

theorem transfer_pullback
    (r : StructureAdditiveSheaf318.pushed f ⟶ StructureAdditiveSheaf318.sheaf Y)
    (h : StructureAdditiveSheaf318.pullback f ≫ r = 𝟙 _)
    (x : structureH Y 1) : transfer f r (SchemeSourceCohomology318.pullback f 1 x) = x := by
  change SheafCohomologyRetraction318.transfer f r 1
    ((equivalence f).symm ((equivalence f) (SheafCohomologyRetraction318.pullback f 1 x))) = x
  rw [AddEquiv.symm_apply_apply,SheafCohomologyRetraction318.transfer_pullback f r h]

end AffineHOneComparison318
