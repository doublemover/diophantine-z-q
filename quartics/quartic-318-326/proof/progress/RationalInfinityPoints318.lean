module
public import InfinityAdditionPoints318
public import RationalCompletedPoints318
public import RationalChordPoints318
public section
noncomputable section
namespace RationalInfinityPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open InfinityAdditionAlgebra318 InfinityAdditionScheme318 InfinityAdditionPoints318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {L:Type} [Field L] [Algebra ℚ L]
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2)))
include hD

/-- The completed Scheme point is bound to the genuine literal elliptic point type. -/
@[expose] def outputPoint (t:Bool)
    (φ:OutputRing A B t →ₐ[ℚ] L) :
    (RationalWeierstrassPoints318.model (K:=L) A B hD).Point :=
  RationalCompletedPoints318.fieldPointEquiv A B hD
    (outputSchemePoint A B t φ)

/-- Every zero-denominator field point of either actual infinity-output chart agrees
with Mathlib's actual inverse-pair addition, including doubling at 2-torsion. -/
theorem zero_denominator_add [DecidableEq L] (t:Bool)
    (φ:OutputRing A B t →ₐ[ℚ] L)
    (hd:φ (pairMap A B t
      (denominator A B t))=0) :
    outputPoint A B hD t φ=
      RationalChordPoints318.pointOfHom A B hD (φ.comp (leftInput A B t))+
      RationalChordPoints318.pointOfHom A B hD (φ.comp (rightInput A B t)) := by
  rw [outputPoint,outputSchemePoint_infinity _ _ _ _ hd,RationalCompletedPoints318.fieldPointEquiv_infinity]
  obtain ⟨hx,hy⟩:=InfinityAdditionValues318.inverse_coordinates _ _ t φ hd
  have ha1 : (RationalWeierstrassPoints318.model (K:=L) A B hD).a₁=0 := by
    simp only [RationalWeierstrassPoints318.model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      map_zero]
  have ha3 : (RationalWeierstrassPoints318.model (K:=L) A B hD).a₃=0 := by
    simp only [RationalWeierstrassPoints318.model,WeierstrassCurve.toAffine,WeierstrassCurve.map,
      map_zero]
  unfold RationalChordPoints318.pointOfHom RationalWeierstrassPoints318.solutionPoint
  simp only [AffineEquationFunctor318.ofHom,AlgHom.comp_apply,leftInput,rightInput]
  change WeierstrassCurve.Affine.Point.zero=
    WeierstrassCurve.Affine.Point.some (φ (pairMap _ _ t (X1 _ _))) (φ (pairMap _ _ t (Y1 _ _))) _+
    WeierstrassCurve.Affine.Point.some (φ (pairMap _ _ t (X2 _ _))) (φ (pairMap _ _ t (Y2 _ _))) _
  symm
  apply WeierstrassCurve.Affine.Point.add_of_Y_eq hx
  simpa only [WeierstrassCurve.Affine.negY,ha1,ha3,zero_mul,sub_zero] using hy

end RationalInfinityPoints318
