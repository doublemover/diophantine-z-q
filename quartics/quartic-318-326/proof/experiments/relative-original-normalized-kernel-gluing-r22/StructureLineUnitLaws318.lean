module
public import StructureLineAutomorphisms318
public section
noncomputable section
namespace StructureLineUnitLaws318
open AlgebraicGeometry CategoryTheory
universe u
variable (X : Scheme.{u})
local notation "O" => SheafOfModules.unit X.ringCatSheaf

lemma iso_one : StructureLineAutomorphisms318.iso X 1=Iso.refl O := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  exact (ClutchedModule318.multiply_top (1:Γ(X,⊤)) 1).trans (mul_one _)

lemma iso_mul (u v : Γ(X,⊤)ˣ) : StructureLineAutomorphisms318.iso X (u*v)=
    StructureLineAutomorphisms318.iso X u ≪≫ StructureLineAutomorphisms318.iso X v := by
  apply Iso.ext
  apply ModuleTopExt318.ext
  change (ClutchedModule318.multiply ((u*v:Γ(X,⊤)ˣ):Γ(X,⊤))).app ⊤ 1=
    (ClutchedModule318.multiply (v:Γ(X,⊤))).app ⊤
      ((ClutchedModule318.multiply (u:Γ(X,⊤))).app ⊤ 1)
  simp only [ClutchedModule318.multiply_top,one_mul,Units.val_mul]

/-- The actual inverse automorphism is multiplication by the actual
inverse global unit, with full sheaf maps retained. -/
lemma iso_inv (u : Γ(X,⊤)ˣ) : StructureLineAutomorphisms318.iso X u⁻¹=
    (StructureLineAutomorphisms318.iso X u).symm := by
  apply Iso.ext
  apply (cancel_epi (StructureLineAutomorphisms318.iso X u).hom).mp
  have h := congrArg Iso.hom (iso_mul X u u⁻¹)
  rw [mul_inv_cancel,iso_one] at h
  simpa only [Iso.trans_hom,Iso.refl_hom,Iso.symm_hom,Iso.hom_inv_id] using h.symm
end StructureLineUnitLaws318
