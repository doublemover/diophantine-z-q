module
public import ContactRelativeTwistCoefficientScalar318
public import OriginalPullbackFrameCocycle318
public import OriginalBinaryFrameComparison318
public section
noncomputable section
namespace ContactRelativeTwistCoefficientIso318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeWholeOpenSections318
open ContactRelativeCoefficientChange318 ContactRelativeGeometricTwist318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (d : ℤ)

lemma opens (i : ULift Bool) : curveMap R S f c ⁻¹ᵁ (line R c d).opens i =
    (line S c d).opens i := by
  rcases i with ⟨i⟩
  cases i
  · exact ContactCoefficientWholeOpens318.finite_preimage R S f c
  · exact ContactCoefficientWholeOpens318.infinity_preimage R S f c

@[expose] def frame (i : ULift Bool) :
    SheafOfModules.unit ((line S c d).opens i).toScheme.ringCatSheaf ≅
      ((Scheme.Modules.pullback (curveMap R S f c)).obj (line R c d).object).restrict
        ((line S c d).opens i).ι :=
  OriginalPullbackFrameCocycle318.frameOn (curveMap R S f c) (line R c d).object
    ((line R c d).opens i) ((line S c d).opens i) (opens R S f c d i) ((line R c d).frame i)

lemma forward :
    (LineFrameCocycle318.cocycle
      ((Scheme.Modules.pullback (curveMap R S f c)).obj (line R c d).object)
      (line S c d).opens (frame R S f c d)).transition ⟨false⟩ ⟨true⟩ =
    (LineFrameCocycle318.cocycle (line S c d).object (line S c d).opens
      (line S c d).frame).transition ⟨false⟩ ⟨true⟩ := by
  rw [OriginalPullbackFrameCocycle318.transition,ContactRelativeTwistPowers318.forward,
    ContactRelativeTwistPowers318.forward]
  exact ContactRelativeTwistCoefficientScalar318.transition R S f c d

/-- The pullback of the original R-geometric twist is the freshly clutched
S-geometric twist, through actual same-cover frame-preserving maps. This
closes the geometric base-change gap rather than assuming line-class equality. -/
@[expose] def iso :
    (Scheme.Modules.pullback (curveMap R S f c)).obj (line R c d).object ≅
      (line S c d).object :=
  OriginalBinaryFrameComparison318.iso _ _ (finiteOpen S c) (infinityOpen S c)
    (frame R S f c d) (line S c d).frame (forward R S f c d) (cover S c)

lemma coordinate (i : ULift Bool) :
    (iso R S f c d).hom ≫
      LineFrameAdjunction318.coordinate (line S c d).object ((line S c d).opens i)
        ((line S c d).frame i) =
      LineFrameAdjunction318.coordinate
        ((Scheme.Modules.pullback (curveMap R S f c)).obj (line R c d).object)
        ((line S c d).opens i) (frame R S f c d i) :=
  OriginalBinaryFrameComparison318.coordinate _ _ _ _ _ _ _ _ i
end ContactRelativeTwistCoefficientIso318
