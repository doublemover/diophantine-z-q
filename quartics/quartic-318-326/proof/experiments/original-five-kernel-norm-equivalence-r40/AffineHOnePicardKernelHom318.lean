module
public import InfinitesimalTensorClass318
public section
noncomputable section
namespace AffineHOnePicardKernelHom318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinitesimalUnitCocycle318 DualNumberScheme318 AffineHOnePointedDeformation318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ base R) (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤)
@[expose] def coefficientCocycle (x : Γ(X,U ⊓ V)) :
    AdditiveCocycle (thickening R p) (thickOpens p U V) :=
  AdditiveCocycleRefinement318.cocycle (pullback.fst p (structureMap R))
    (TwoOpenAdditiveCocycle318.opens U V) (thickOpens p U V) (fun _ => le_rfl)
    (TwoOpenAdditiveCocycle318.cocycle U V x)
lemma coefficient_add (x y : Γ(X,U ⊓ V)) :
    coefficientCocycle p U V (x + y) =
      AdditiveCocycleSum318.add _ (coefficientCocycle p U V x) (coefficientCocycle p U V y) := by
  unfold coefficientCocycle
  rw [AdditiveCocycleSum318.twoOpen_add, AdditiveCocycleSum318.pullback_add]
/-- The underlying class is the existing line-sheaf class of the existing
pointed representative, with the original tensor group law. -/
lemma representative_add (x y : Γ(X,U ⊓ V)) :
    PointedLineDeformation318.forget (reduction R p) (representativeClass p U V h (x + y)) =
      PointedLineDeformation318.forget (reduction R p) (representativeClass p U V h x) *
      PointedLineDeformation318.forget (reduction R p) (representativeClass p U V h y) := by
  change LineSheafClass318.classOf (line _ (DualNumberInfinitesimalLines318.epsilon R p)
      (DualNumberInfinitesimalLines318.epsilon_square R p) _
      (coefficientCocycle p U V (x + y)) (thick_cover p U V h)) =
    LineSheafClass318.classOf (line _ (DualNumberInfinitesimalLines318.epsilon R p)
      (DualNumberInfinitesimalLines318.epsilon_square R p) _
      (coefficientCocycle p U V x) (thick_cover p U V h)) *
    LineSheafClass318.classOf (line _ (DualNumberInfinitesimalLines318.epsilon R p)
      (DualNumberInfinitesimalLines318.epsilon_square R p) _
      (coefficientCocycle p U V y) (thick_cover p U V h))
  rw [coefficient_add]
  exact InfinitesimalTensorClass318.class_add _ _ _ _ _ _ _
@[expose] def oldClass (z : SheafCohomologyRetraction318.structureH X 1) :
    LineSheafClass318.Class (thickening R p) :=
  PointedLineDeformation318.forget (reduction R p)
    (AffineHOnePointedDeformation318.map p U V hU hV h z)
lemma oldClass_add (x y : SheafCohomologyRetraction318.structureH X 1) :
    oldClass p U V hU hV h (x + y) =
      oldClass p U V hU hV h x * oldClass p U V hU hV h y := by
  obtain ⟨a,rfl⟩ := AffineCoverHOnePresentation318.boundary_surjective U V hU hV h x
  obtain ⟨b,rfl⟩ := AffineCoverHOnePresentation318.boundary_surjective U V hU hV h y
  unfold oldClass
  rw [← map_add, map_boundary, map_boundary, map_boundary]
  exact representative_add p U V h a b
lemma oldClass_zero : oldClass p U V hU hV h 0 = 1 := by
  have hh := oldClass_add p U V hU hV h 0 0
  rw [zero_add] at hh
  have hh' : oldClass p U V hU hV h 0 * 1 =
      oldClass p U V hU hV h 0 * oldClass p U V hU hV h 0 := by simpa using hh
  exact (mul_left_cancel hh').symm
/-- An actual homomorphism into the ORIGINAL line-class group. Multiplicative
only changes notation on original additive H1; it does not replace its carrier. -/
@[expose] def hom : Multiplicative (SheafCohomologyRetraction318.structureH X 1) →*
    LineSheafClass318.Class (thickening R p) where
  toFun z := oldClass p U V hU hV h z.toAdd
  map_one' := oldClass_zero p U V hU hV h
  map_mul' x y := oldClass_add p U V hU hV h x.toAdd y.toAdd
lemma hom_apply (z : SheafCohomologyRetraction318.structureH X 1) :
    hom p U V hU hV h (Multiplicative.ofAdd z) =
      PointedLineDeformation318.forget (reduction R p)
        (AffineHOnePointedDeformation318.map p U V hU hV h z) := rfl
/-- The codomain is the genuine kernel subgroup of the OLD pullback homomorphism. -/
@[expose] def kernelHom : Multiplicative (SheafCohomologyRetraction318.structureH X 1) →*
    (LineClassPullbackHom318.pullback (reduction R p)).ker where
  toFun z := ⟨hom p U V hU hV h z,
    PointedLineDeformation318.special_fiber_trivial (reduction R p)
      (AffineHOnePointedDeformation318.map p U V hU hV h z.toAdd)⟩
  map_one' := Subtype.ext (map_one (hom p U V hU hV h))
  map_mul' x y := Subtype.ext (map_mul (hom p U V hU hV h) x y)
lemma kernelHom_val (z : SheafCohomologyRetraction318.structureH X 1) :
    (kernelHom p U V hU hV h (Multiplicative.ofAdd z)).val =
      PointedLineDeformation318.forget (reduction R p)
        (AffineHOnePointedDeformation318.map p U V hU hV h z) := rfl
lemma oldClass_neg (z : SheafCohomologyRetraction318.structureH X 1) :
    oldClass p U V hU hV h (-z) = (oldClass p U V hU hV h z)⁻¹ :=
  map_inv (hom p U V hU hV h) (Multiplicative.ofAdd z)
lemma oldClass_nsmul (n : ℕ) (z : SheafCohomologyRetraction318.structureH X 1) :
    oldClass p U V hU hV h (n • z) = (oldClass p U V hU hV h z)^n :=
  map_pow (hom p U V hU hV h) (Multiplicative.ofAdd z) n
end AffineHOnePicardKernelHom318
