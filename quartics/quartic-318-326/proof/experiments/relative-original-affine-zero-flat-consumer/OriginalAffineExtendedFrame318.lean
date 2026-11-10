module
public import OriginalAffineLinePathSections318
public import ScalarExtensionTensor318
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public section
noncomputable section
namespace OriginalAffineExtendedFrame318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct ChangeOfRings
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (B C : CommRingCat.{u}) (k : B ⟶ C)
local instance : Algebra B C := k.hom.toAlgebra
variable (N : Line (Spec B)) (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B)
local notation "M" => OriginalLineAffineModel318.sections B N

@[expose] def tensorFrame : C ⊗[B] M ≃ₗ[C] C where
  __ := ((Algebra.linearMap B C).comp v.toLinearMap).liftBaseChange C
  invFun c := c ⊗ₜ[B] v.symm 1
  left_inv z := by
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
        change (c * k.hom (v m)) ⊗ₜ[B] v.symm 1 = c ⊗ₜ[B] m
        have hm : m = v m • v.symm 1 := by apply v.injective; simp
        conv_rhs => rw [hm]
        rw [TensorProduct.tmul_smul,TensorProduct.smul_tmul']
        congr 1
        change c * k.hom (v m) = k.hom (v m) * c
        exact mul_comm _ _
    | add x y hx hy => simp only [map_add,TensorProduct.add_tmul,hx,hy]
  right_inv c := by
    change c * k.hom (v (v.symm 1))=c
    rw [LinearEquiv.apply_symm_apply,map_one,mul_one]

abbrev pulled := LineSheafPullback318.line (Spec.map k) N

/-- The actual scalar-extended frame on the literal geometric pulled line,
constructed through the unchanged original affine section comparison. -/
@[expose] def frame : OriginalLineAffineModel318.sections C (pulled B C k N) ≃ₗ[C] C :=
  (OriginalLineAffineBaseChange318.sectionsIso k N).toLinearEquiv.symm.trans
    ((ScalarExtensionTensor318.tensorEquiv (S:=B) (T:=C) M).trans (tensorFrame B C k N v))

lemma frame_unit (m : M) :
    frame B C k N v
      (OriginalAffineLinePathSections318.restriction k N (pulled B C k N) (Iso.refl _) m)=k.hom (v m) := by
  rw [← OriginalAffineLinePathSections318.unit_apply]
  change tensorFrame B C k N v (ScalarExtensionTensor318.tensorEquiv M
    ((OriginalLineAffineBaseChange318.sectionsIso k N).toLinearEquiv.symm
      ((OriginalLineAffineBaseChange318.sectionsIso k N).toLinearEquiv
        ((ModuleCat.extendRestrictScalarsAdj k.hom).unit.app _ m)))) = _
  rw [LinearEquiv.symm_apply_apply]
  change (1:C) * k.hom (v m)=k.hom (v m)
  exact one_mul _
end OriginalAffineExtendedFrame318
