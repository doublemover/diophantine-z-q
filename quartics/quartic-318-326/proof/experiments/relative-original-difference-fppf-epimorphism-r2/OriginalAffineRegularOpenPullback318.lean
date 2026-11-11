module
public import OriginalAffineExtendedFrame318
public import SectionZeroRegularCoordinate318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public section
noncomputable section
namespace OriginalAffineRegularOpenPullback318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B : CommRingCat.{u}) (f : A ⟶ B) [IsOpenImmersion (Spec.map f)]
local instance : Algebra A B := f.hom.toAlgebra

/-- Flatness here is PROVED for an existing open immersion. It is not
an assumption that the zero family is flat over its parameter space. -/
lemma scalar_flat : Module.Flat A B := by
  have hf : f.hom.Flat := AlgebraicGeometry.Flat.SpecMap_iff.mp inferInstance
  change (algebraMap A B).Flat at hf
  exact RingHom.flat_algebraMap_iff.mp hf

variable (L : Line (Spec A))
  (e : OriginalLineAffineModel318.sections A L ≃ₗ[A] A)
  (s : OriginalLineAffineModel318.sections A L)
  (hr : SectionZeroRegularCoordinate318.Regular A (OriginalLineAffineModel318.sections A L) s)
local notation "N" => LineSheafPullback318.line (Spec.map f) L

/-- A regular ORIGINAL section stays regular on every actual affine open
refinement. The proof uses the genuine extended frame and its exact unit
coordinate, then flatness of the open immersion to preserve its nonzerodivisor. -/
lemma regular : SectionZeroRegularCoordinate318.Regular B
    (OriginalLineAffineModel318.sections B N)
    (OriginalAffineLinePathSections318.restriction f L N (Iso.refl _) s) := by
  haveI : Module.Flat A B := scalar_flat A B f
  have h := (SectionZeroRegularCoordinate318.regular_iff A
    (OriginalLineAffineModel318.sections A L) s e).mp hr
  have hc : e s ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_left]
    intro a ha
    exact h a (by simpa only [mul_comm] using ha)
  apply (SectionZeroRegularCoordinate318.regular_iff B
    (OriginalLineAffineModel318.sections B N) _
    (OriginalAffineExtendedFrame318.frame A B f L e)).mpr
  intro b hb
  rw [OriginalAffineExtendedFrame318.frame_unit] at hb
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M:=B) hc
  change f.hom (e s) * b=f.hom (e s) * 0
  simpa only [mul_comm,mul_zero] using hb
end OriginalAffineRegularOpenPullback318
