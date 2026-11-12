module
public import ContactRelativeOriginalProjection318
public section
noncomputable section
namespace ContactRelativeOriginalTwistIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeWholeOpenSections318
open ContactRelativeOriginalProjection318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (d : ℤ)

lemma old_forward :
    (LineFrameCocycle318.cocycle (ContactOriginalTwistingLine318.line c d).object
      (ContactOriginalTwistingLine318.line c d).opens
      (ContactOriginalTwistingLine318.line c d).frame).transition ⟨false⟩ ⟨true⟩ =
      ContactOriginalTwistingLine318.transitionUnit c d := by
  apply Units.ext
  change (OpenLineFrameCoordinates318.frame (ContactOriginalTwistingLine318.line c d).object
    (ContactOriginalWholeRestriction318.finiteOpen c)
    (ContactOriginalTwistingLine318.finiteFrame c d).symm _ inf_le_left).symm
      (OpenLineFrameCoordinates318.frame (ContactOriginalTwistingLine318.line c d).object
        (ContactOriginalWholeRestriction318.infinityOpen c)
        (ContactOriginalTwistingLine318.infinityFrame c d).symm _ inf_le_right 1) = _
  rw [OriginalClutchedFrameTransition318.inverse_relation,LinearEquiv.symm_apply_apply,one_mul]
  rfl

lemma opens (i : ULift Bool) : projection R c ⁻¹ᵁ (ContactOriginalTwistingLine318.line c d).opens i =
    (ContactRelativeGeometricTwist318.line R c d).opens i := by
  rcases i with ⟨i⟩
  cases i
  · exact finite_preimage R c
  · exact infinity_preimage R c

@[expose] def frame (i : ULift Bool) :
    SheafOfModules.unit ((ContactRelativeGeometricTwist318.line R c d).opens i).toScheme.ringCatSheaf ≅
      ((Scheme.Modules.pullback (projection R c)).obj (ContactOriginalTwistingLine318.line c d).object).restrict
        ((ContactRelativeGeometricTwist318.line R c d).opens i).ι :=
  OriginalPullbackFrameCocycle318.frameOn (projection R c) (ContactOriginalTwistingLine318.line c d).object
    ((ContactOriginalTwistingLine318.line c d).opens i)
    ((ContactRelativeGeometricTwist318.line R c d).opens i) (opens R c d i)
    ((ContactOriginalTwistingLine318.line c d).frame i)

lemma forward :
    (LineFrameCocycle318.cocycle
      ((Scheme.Modules.pullback (projection R c)).obj (ContactOriginalTwistingLine318.line c d).object)
      (ContactRelativeGeometricTwist318.line R c d).opens (frame R c d)).transition ⟨false⟩ ⟨true⟩ =
    (LineFrameCocycle318.cocycle (ContactRelativeGeometricTwist318.line R c d).object
      (ContactRelativeGeometricTwist318.line R c d).opens
      (ContactRelativeGeometricTwist318.line R c d).frame).transition ⟨false⟩ ⟨true⟩ := by
  rw [OriginalPullbackFrameCocycle318.transition,old_forward,ContactRelativeTwistPowers318.forward]
  exact transition R c d

/-- The actual relative geometric twist is the pullback of the specified
ORIGINAL rational geometric twist, with both full chart frames retained. -/
@[expose] def iso :
    (Scheme.Modules.pullback (projection R c)).obj (ContactOriginalTwistingLine318.line c d).object ≅
      (ContactRelativeGeometricTwist318.line R c d).object :=
  OriginalBinaryFrameComparison318.iso _ _ (finiteOpen R c) (infinityOpen R c)
    (frame R c d) (ContactRelativeGeometricTwist318.line R c d).frame (forward R c d) (cover R c)

lemma coordinate (i : ULift Bool) :
    (iso R c d).hom ≫ LineFrameAdjunction318.coordinate
      (ContactRelativeGeometricTwist318.line R c d).object
      ((ContactRelativeGeometricTwist318.line R c d).opens i)
      ((ContactRelativeGeometricTwist318.line R c d).frame i) =
    LineFrameAdjunction318.coordinate
      ((Scheme.Modules.pullback (projection R c)).obj (ContactOriginalTwistingLine318.line c d).object)
      ((ContactRelativeGeometricTwist318.line R c d).opens i) (frame R c d i) :=
  OriginalBinaryFrameComparison318.coordinate _ _ _ _ _ _ _ _ i
end ContactRelativeOriginalTwistIso318
