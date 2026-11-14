module
public import OriginalInverseLineCancellationCoherence318
public section
noncomputable section
namespace OriginalTensorConjugation318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {I I' M M' N N' : X.Modules}
/-- Exact tensor naturality through the specified native object
comparisons. The middle inverse cancels on the SAME original module. -/
lemma square (a : I ≅ I') (b : M ≅ M') (c : N ≅ N') (e : M ≅ N) :
    TensorSheafFunctor318.congr a b ≪≫
      TensorSheafFunctor318.congr (Iso.refl I') (b.symm ≪≫ e ≪≫ c)=
    TensorSheafFunctor318.congr (Iso.refl I) e ≪≫ TensorSheafFunctor318.congr a c := by
  rw [←OriginalTensorChartFrameNaturality318.congr_trans,
    ←OriginalTensorChartFrameNaturality318.congr_trans]
  simp only [Iso.trans_refl,Iso.refl_trans]
  congr 1
  apply Iso.ext
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id_assoc]

/-- Inverse face of a specified actual cancellation square. -/
lemma inverse_cancel {A B C : X.Modules} (a : A ≅ B) (b : B ≅ C) (c : A ≅ C)
    (h : a ≪≫ b=c) : b.inv=c.inv ≫ a.hom := by
  have hh := congrArg Iso.hom h
  change a.hom ≫ b.hom=c.hom at hh
  apply (cancel_mono b.hom).mp
  rw [Category.assoc,hh,c.inv_hom_id,b.inv_hom_id]
end OriginalTensorConjugation318
