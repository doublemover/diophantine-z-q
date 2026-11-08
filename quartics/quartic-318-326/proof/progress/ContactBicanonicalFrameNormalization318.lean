module
public import TensorSheafNormalization318
public import ContactBicanonicalLocalSections318
public section
noncomputable section
namespace ContactBicanonicalFrameNormalization318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The actual bicanonical frame sends each genuine pure tensor to the
product of its two intrinsic differential-frame coefficients. -/
theorem localFrame_pure (i : Option (Fin 4)) (U : (ContactIntrinsicFrames318.chart c i).Opens)
    (m n : Γ(ContactIntrinsicDifferentials318.omega c,
      (ContactIntrinsicFrames318.embedding c i).opensFunctor.obj U)) :
    (ContactBicanonicalSheaf318.localFrame c i).hom.app U
      (IntrinsicTensorSheaf318.pure (ContactIntrinsicDifferentials318.omega c)
        (ContactIntrinsicDifferentials318.omega c)
        ((ContactIntrinsicFrames318.embedding c i).opensFunctor.obj U) m n) =
      (show Γ(ContactIntrinsicFrames318.chart c i,U) from
        (ContactIntrinsicFrames318.localFrame c i).hom.app U m) *
        (show Γ(ContactIntrinsicFrames318.chart c i,U) from
          (ContactIntrinsicFrames318.localFrame c i).hom.app U n) := by
  change TensorSheafFunctor318.unitIso.hom.app U
    ((TensorSheafFunctor318.congr (ContactIntrinsicFrames318.localFrame c i)
      (ContactIntrinsicFrames318.localFrame c i)).hom.app U
      ((TensorOpenRestriction318.iso (ContactIntrinsicFrames318.embedding c i)
        (ContactIntrinsicDifferentials318.omega c) (ContactIntrinsicDifferentials318.omega c)).hom.app U
        (IntrinsicTensorSheaf318.pure _ _ _ m n))) = _
  rw [TensorSheafNormalization318.restriction_pure,
    TensorSheafNormalization318.congr_pure,TensorSheafNormalization318.unitIso_pure]
end ContactBicanonicalFrameNormalization318
