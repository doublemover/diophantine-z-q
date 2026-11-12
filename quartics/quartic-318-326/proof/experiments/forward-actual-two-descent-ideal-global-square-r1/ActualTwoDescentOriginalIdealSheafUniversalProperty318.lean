module
public import ActualTwoDescentOriginalDegreeZeroIdealSheaf318
public section
noncomputable section
namespace ActualTwoDescentOriginalIdealSheafUniversalProperty318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalInverseInfinityTransition318
variable {K : Type*} [Field K] [CharZero K]

/-- Descent of actual morphisms into the two specified coefficient
sheaves, with equality in the SAME original common-chart sheaf. -/
def idealSheafLift (n : K) (i : Fin 3) {M : (originalCubicScheme n).Modules}
    (f : M ⟶ affineIdealPushed n i) (g : M ⟶ infinityInversePushed n)
    (h : f ≫ affineIdealRestriction n i=g ≫ infinityInverseRestriction n) :
    M ⟶ originalRootIdealSheaf n i := pullback.lift f g h
lemma actual_ideal_sheaf_lift_affine (n : K) (i : Fin 3) {M : (originalCubicScheme n).Modules}
    (f : M ⟶ affineIdealPushed n i) (g : M ⟶ infinityInversePushed n)
    (h : f ≫ affineIdealRestriction n i=g ≫ infinityInverseRestriction n) :
    idealSheafLift n i f g h ≫ affineProjection n i=f := pullback.lift_fst _ _ _
lemma actual_ideal_sheaf_lift_infinity (n : K) (i : Fin 3) {M : (originalCubicScheme n).Modules}
    (f : M ⟶ affineIdealPushed n i) (g : M ⟶ infinityInversePushed n)
    (h : f ≫ affineIdealRestriction n i=g ≫ infinityInverseRestriction n) :
    idealSheafLift n i f g h ≫ infinityProjection n i=g := pullback.lift_snd _ _ _
lemma actual_ideal_sheaf_hom_ext (n : K) (i : Fin 3) {M : (originalCubicScheme n).Modules}
    (f g : M ⟶ originalRootIdealSheaf n i)
    (ha : f ≫ affineProjection n i=g ≫ affineProjection n i)
    (hi : f ≫ infinityProjection n i=g ≫ infinityProjection n i) : f=g :=
  pullback.hom_ext ha hi

/-- Exact infinity-side coefficient normalization on global sections.
The sign is observable in the produced sheaf map, not just its name. -/
lemma actual_infinity_inverse_restriction_top (n : K) (b : Γ(infinityScheme n,⊤)) :
    (infinityInverseRestriction n).app ⊤ b=(intoInfinity n).appTop b*inverseUSection n :=
  ClutchedModule318.twistedRestriction_top _ _ _ _ _ _ b
end ActualTwoDescentOriginalIdealSheafUniversalProperty318
