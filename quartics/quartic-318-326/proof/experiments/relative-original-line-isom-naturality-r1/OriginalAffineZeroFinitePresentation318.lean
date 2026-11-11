module
public import OriginalAffineSectionZero318
public import SectionZeroFinitePresentation318
public import SectionZeroRegularCoordinate318
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public section
noncomputable section
namespace OriginalAffineZeroFinitePresentation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (R : CommRingCat.{u}) (L : Line (Spec R))
local instance : Module.FinitePresentation R (OriginalLineAffineModel318.sections R L) :=
  (OriginalLineAffineModel318.properties R L).1
variable (s : OriginalLineAffineModel318.sections R L)

lemma ideal_fg : (OriginalAffineSectionZero318.ideal R L s).FG :=
  SectionZeroFinitePresentation318.ideal_fg R _ s

instance finitePresentation : LocallyOfFinitePresentation (OriginalAffineSectionZero318.into R L s) := by
  apply LocallyOfFinitePresentation.SpecMap_iff.mpr
  apply RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  exact ideal_fg R L s

/-- Any genuine original affine rank-one section frame gives exactly the
principal equation of the same original zero quotient and its intrinsic
regularity criterion. The frame and regularity are not assumed to exist globally. -/
lemma exact_frame (e : OriginalLineAffineModel318.sections R L ≃ₗ[R] R) :
    OriginalAffineSectionZero318.ideal R L s = Ideal.span {e s} ∧
    (SectionZeroRegularCoordinate318.Regular R _ s ↔ ∀ a : R,a * e s=0 → a=0) :=
  ⟨SectionZeroRegularCoordinate318.ideal_in_frame R _ s e,
    SectionZeroRegularCoordinate318.regular_iff R _ s e⟩
end OriginalAffineZeroFinitePresentation318
