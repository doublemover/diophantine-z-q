module
public import ContactBicanonicalFrameNormalization318
public import IntrinsicFrameDerivative318
public section
noncomputable section
namespace ContactBicanonicalDerivative318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 80000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

/-- The normalized intrinsic local generator. Its equality with the
actual universal chart-coordinate derivative is supplied separately. -/
@[expose] def localDerivative (i : Option (Fin 4)) :=
  (ContactIntrinsicFrames318.localFrame c i).inv.app ⊤
    (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from 1)

theorem localDerivative_normalized (i : Option (Fin 4)) :
    (ContactIntrinsicFrames318.localFrame c i).hom.app ⊤ (localDerivative c i)=
      (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from 1) := by
  exact congrArg (fun f => f.app ⊤
    (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from 1))
      (ContactIntrinsicFrames318.localFrame c i).inv_hom_id

/-- The square of the normalized intrinsic local differential generator, as a section of the genuine tensor-square sheaf. -/
@[expose] def localSquare (i : Option (Fin 4)) :
    Γ((ContactBicanonicalSheaf318.bicanonical c).restrict
      (ContactIntrinsicFrames318.embedding c i),⊤) :=
  IntrinsicTensorSheaf318.pure (ContactIntrinsicDifferentials318.omega c)
    (ContactIntrinsicDifferentials318.omega c)
    ((ContactIntrinsicFrames318.embedding c i).opensFunctor.obj ⊤)
    (localDerivative c i) (localDerivative c i)

theorem localSquare_normalized (i : Option (Fin 4)) :
    (ContactBicanonicalSheaf318.localFrame c i).hom.app ⊤ (localSquare c i)=
      (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from 1) := by
  change (ContactBicanonicalSheaf318.localFrame c i).hom.app ⊤
    (IntrinsicTensorSheaf318.pure _ _ _ _ _) = _
  rw [ContactBicanonicalFrameNormalization318.localFrame_pure,
    localDerivative_normalized,mul_one]

/-- The genuine inverse bicanonical frame is exactly the square of the
normalized intrinsic local differential generator, with scalar one. -/
theorem frame_inverse_one (i : Option (Fin 4)) :
    (ContactBicanonicalSheaf318.localFrame c i).inv.app ⊤
      (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from 1)=localSquare c i := by
  apply (ConcreteCategory.bijective_of_isIso
    ((ContactBicanonicalSheaf318.localFrame c i).hom.app ⊤)).1
  have h := congrArg (fun f => f.app ⊤
    (show Γ(ContactIntrinsicFrames318.chart c i,⊤) from 1))
      (ContactBicanonicalSheaf318.localFrame c i).inv_hom_id
  exact h.trans (localSquare_normalized c i).symm
end ContactBicanonicalDerivative318
