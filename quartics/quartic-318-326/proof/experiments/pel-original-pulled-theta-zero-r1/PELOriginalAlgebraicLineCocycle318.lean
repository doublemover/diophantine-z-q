module
public import PELOriginalAlgebraicPolarizationLine318
public import OriginalOpenCoefficientSpecialization318
public section
noncomputable section
namespace PELOriginalAlgebraicLineCocycle318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The actual cubic frame transition is the coefficient of the SAME
right coordinate section in the left frame, in the original overlap ring. -/
theorem cubic_transition_value (a b : NonemptyIndex τ hτ) :
    ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (opens τ hτ)
      (cubicFrame τ hτ)).transition a b).val =
    GlobalSectionFrameCoordinates318.coefficient (opens τ hτ a)
      (cubic τ hτ a.val b.val.1) (opens τ hτ a ⊓ opens τ hτ b) inf_le_left := by
  apply GlobalSectionFrameCocycle318.transition_value _ _ _
    (cubicSection τ hτ b.val.1) a b _ (cubic_section_coefficient τ hτ a b.val.1)
  simpa only [cubic_self,GlobalScalarSheafEndomorphism318.endomorphism_one,
    Category.id_comp] using cubic_section_coefficient τ hτ b b.val.1

theorem quadratic_transition_value (a b : NonemptyIndex τ hτ) :
    ((LineFrameCocycle318.cocycle (quadraticSheaf τ hτ) (opens τ hτ)
      (quadraticFrame τ hτ)).transition a b).val =
    GlobalSectionFrameCoordinates318.coefficient (opens τ hτ a)
      (quadratic τ hτ a.val b.val.2) (opens τ hτ a ⊓ opens τ hτ b) inf_le_left := by
  apply GlobalSectionFrameCocycle318.transition_value _ _ _
    (quadraticSection τ hτ b.val.2) a b _ (quadratic_section_coefficient τ hτ a b.val.2)
  simpa only [quadratic_self,GlobalScalarSheafEndomorphism318.endomorphism_one,
    Category.id_comp] using quadratic_section_coefficient τ hτ b b.val.2

/-- Exact regular-function transition after the canonical original-open
comparison. This is an identity on the WHOLE overlap, before any complex
point is introduced. -/
theorem cubic_transition_pullback (a b : NonemptyIndex τ hτ) :
    (LineFrameTopScalar318.ringTop (opens τ hτ a ⊓ opens τ hτ b)).inv
      ((LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (opens τ hτ)
        (cubicFrame τ hτ)).transition a b).val =
      (toLeft τ hτ a.val b.val).appTop (cubic τ hτ a.val b.val.1) := by
  rw [cubic_transition_value]
  exact OriginalOpenCoefficientSpecialization318.coefficient_pullback _ _ _ _

theorem quadratic_transition_pullback (a b : NonemptyIndex τ hτ) :
    (LineFrameTopScalar318.ringTop (opens τ hτ a ⊓ opens τ hτ b)).inv
      ((LineFrameCocycle318.cocycle (quadraticSheaf τ hτ) (opens τ hτ)
        (quadraticFrame τ hτ)).transition a b).val =
      (toLeft τ hτ a.val b.val).appTop (quadratic τ hτ a.val b.val.2) := by
  rw [quadratic_transition_value]
  exact OriginalOpenCoefficientSpecialization318.coefficient_pullback _ _ _ _

/-- The actual ring homomorphism specializing an original-open function
through an actual Spec(C) point. All three scalar comparisons are retained. -/
@[expose] def evaluation (a b : NonemptyIndex τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (opens τ hτ a ⊓ opens τ hτ b).toScheme) :
    Γ(candidate τ hτ,opens τ hτ a ⊓ opens τ hτ b) →+* ℂ :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp p.appTop.hom).comp
    (LineFrameTopScalar318.ringTop (opens τ hτ a ⊓ opens τ hτ b)).inv.hom

/-- The algebraic degree-one transition evaluates to the quotient of
already constructed regular cubic and quadratic coefficients. -/
theorem transition_evaluation (a b : NonemptyIndex τ hτ)
    (p : Spec (CommRingCat.of ℂ) ⟶ (opens τ hτ a ⊓ opens τ hτ b).toScheme) :
    evaluation τ hτ a b p
      ((LineFrameCocycle318.cocycle (sheaf τ hτ) (opens τ hτ)
        (line τ hτ).frame).transition a b).val =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((p ≫ toLeft τ hτ a.val b.val).appTop (cubic τ hτ a.val b.val.1)) /
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((p ≫ toLeft τ hτ a.val b.val).appTop (quadratic τ hτ a.val b.val.2)) := by
  rw [PELOriginalAlgebraicPolarizationLine318.transition]
  rw [div_eq_mul_inv]
  change _ = _ * _⁻¹
  simp only [Units.val_mul]
  rw [map_mul]
  have hi : evaluation τ hτ a b p
      (((LineFrameCocycle318.cocycle (quadraticSheaf τ hτ) (opens τ hτ)
        (quadraticFrame τ hτ)).transition a b)⁻¹).val =
      (evaluation τ hτ a b p
        ((LineFrameCocycle318.cocycle (quadraticSheaf τ hτ) (opens τ hτ)
          (quadraticFrame τ hτ)).transition a b).val)⁻¹ := by
    simpa only [Units.coe_map,Units.val_inv_eq_inv_val] using
      congrArg Units.val (map_inv (Units.map (evaluation τ hτ a b p).toMonoidHom) _)
  rw [hi]
  congr 1
  · change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop _).inv _)) = _
    rw [cubic_transition_pullback]
    rfl
  · congr 1
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
      ((LineFrameTopScalar318.ringTop _).inv _)) = _
    rw [quadratic_transition_pullback]
    rfl
end PELOriginalAlgebraicLineCocycle318
