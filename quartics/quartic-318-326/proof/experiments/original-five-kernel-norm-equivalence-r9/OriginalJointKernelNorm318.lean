module
public import OriginalKernelNormHom318
public import MultiplicativeRationalEighth318
public section
noncomputable section
namespace OriginalJointKernelNorm318
open OriginalFiveKernelCoordinates318 ActualFiveHOneDecomposition318 ActualSourceHOnePullbacks318
open scoped BigOperators
@[expose] def joint : SourceKernel →* ((i : Index) → TargetKernel i) where
  toFun L i := OriginalKernelNormHom318.hom i L
  map_one' := by funext i; exact map_one (OriginalKernelNormHom318.hom i)
  map_mul' L M := by funext i; exact map_mul (OriginalKernelNormHom318.hom i) L M
/-- The actual first-order source kernel is uniquely eighth-divisible. -/
@[expose] def eighth : SourceKernel ≃* SourceKernel :=
  source.symm.trans ((MultiplicativeRationalEighth318.equivalence SourceHOne).trans source)
lemma eighth_apply (L : SourceKernel) : eighth L = L ^ 8 := by
  change source (MultiplicativeRationalEighth318.equivalence SourceHOne (source.symm L)) = _
  rw [MultiplicativeRationalEighth318.apply_pow,map_pow,MulEquiv.apply_symm_apply]
/-- Tensor pullbacks after the genuine joint RAW norm are the eighth power,
not the identity and not an unspecified isogeny normalization. -/
lemma product_joint (L : SourceKernel) : OriginalFiveKernelDecomposition318.product (joint L) = eighth L := by
  rw [eighth_apply]
  exact OriginalFiveKernelDecomposition318.product_norms L
/-- The actual raw norm vector is an equivalence on the WHOLE first-order
kernel. This is NOT a represented Jacobian norm or a global Picard isogeny. -/
@[expose] def equivalence : SourceKernel ≃* ((i : Index) → TargetKernel i) :=
  eighth.trans OriginalFiveKernelDecomposition318.equivalence.symm
lemma equivalence_apply (L : SourceKernel) : equivalence L = joint L := by
  apply OriginalFiveKernelDecomposition318.equivalence.injective
  change OriginalFiveKernelDecomposition318.equivalence
    (OriginalFiveKernelDecomposition318.equivalence.symm (eighth L)) =
      OriginalFiveKernelDecomposition318.product (joint L)
  rw [MulEquiv.apply_symm_apply,product_joint]
lemma joint_bijective : Function.Bijective joint := by
  have h : (joint : SourceKernel → ((i : Index) → TargetKernel i)) = equivalence :=
    funext (fun L => (equivalence_apply L).symm)
  rw [h]
  exact equivalence.bijective
/-- Both inverse maps are explicit: tensor the original five pullbacks,
then take the UNIQUE eighth root in the actual first-order source kernel. -/
lemma inverse_apply (x : (i : Index) → TargetKernel i) :
    equivalence.symm x = eighth.symm (∏ i,OriginalFiveKernelCoordinates318.pullback i (x i)) := rfl
lemma jointly_detect (L M : SourceKernel)
    (h : ∀ i, norm i L = norm i M) : L = M :=
  joint_bijective.1 (funext h)
end OriginalJointKernelNorm318
