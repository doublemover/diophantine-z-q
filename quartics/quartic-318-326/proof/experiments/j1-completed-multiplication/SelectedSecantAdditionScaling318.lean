module
public import SelectedShortAffineScaling318
public import RelativeChordScheme318
public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace SelectedSecantAdditionScaling318
open ShortAffineJacobian318 RelativeChordAlgebra318
variable {R : Type u} [CommRing R]
variable (A B C D : R) (r : Rˣ)
variable (hA : A = (r:R)^4*C) (hB : B = (r:R)^6*D)
local notation "f" => SelectedShortAffineScaling318.hom A B C D r hA hB
local notation "s" => algebraMap R (ChordRing C D) (r:R)

/-- Both genuine input projections are composed with the same actual
affine scaling, in the same order as the original localization. -/
@[expose] def inputs : PairRing A B →ₐ[R] ChordRing C D :=
  Algebra.TensorProduct.lift ((left C D).comp f) ((right C D).comp f) (fun _ _ => Commute.all _ _)

private theorem inputs_left (z : Ring A B) :
    inputs A B C D r hA hB (leftPair A B z) = left C D (f z) := by
  change inputs A B C D r hA hB (z ⊗ₜ[R] (1:Ring A B)) = _
  simp only [inputs,Algebra.TensorProduct.lift_tmul,AlgHom.comp_apply,map_one,mul_one]

private theorem inputs_right (z : Ring A B) :
    inputs A B C D r hA hB (rightPair A B z) = right C D (f z) := by
  change inputs A B C D r hA hB ((1:Ring A B) ⊗ₜ[R] z) = _
  simp only [inputs,Algebra.TensorProduct.lift_tmul,AlgHom.comp_apply,map_one,one_mul]

private theorem scale_isUnit : IsUnit s := r.isUnit.map (algebraMap R (ChordRing C D))

theorem gap_image :
    inputs A B C D r hA hB (gap A B) = s^2 * (x2 C D-x1 C D) := by
  simp only [gap,map_sub,inputs_right,inputs_left,SelectedShortAffineScaling318.hom_x,
    map_mul,map_pow,AlgHom.commutes,x1,x2] <;> ring

/-- Pullback between the actual ordinary chord principal opens. The gap
is multiplied by the square of a unit, so it is exactly the same open. -/
@[expose] def chordHom : ChordRing A B →ₐ[R] ChordRing C D :=
  IsLocalization.Away.liftAlgHom (f := inputs A B C D r hA hB) (gap A B) (by
    rw [gap_image]
    exact ((scale_isUnit C D r).pow 2).mul (gap_unit C D))

private theorem chordHom_map (z : PairRing A B) :
    chordHom A B C D r hA hB (algebraMap (PairRing A B) (ChordRing A B) z) =
      inputs A B C D r hA hB z := by
  simp [chordHom,IsLocalization.Away.liftAlgHom_apply]

local notation "F" => chordHom A B C D r hA hB

/-- Actual first projection on the two secant localizations. -/
theorem left_projection : F.comp (left A B) = (left C D).comp f := by
  apply AlgHom.ext
  intro z
  change F (algebraMap (PairRing A B) (ChordRing A B) (leftPair A B z)) = _
  rw [chordHom_map,inputs_left] <;> rfl

/-- Actual second projection on the two secant localizations. -/
theorem right_projection : F.comp (right A B) = (right C D).comp f := by
  apply AlgHom.ext
  intro z
  change F (algebraMap (PairRing A B) (ChordRing A B) (rightPair A B z)) = _
  rw [chordHom_map,inputs_right] <;> rfl

theorem x1_image : F (x1 A B) = s^2 * x1 C D := by
  change F (algebraMap (PairRing A B) (ChordRing A B) (leftPair A B (x A B))) = _
  simp only [chordHom_map,inputs_left,SelectedShortAffineScaling318.hom_x,map_mul,map_pow,
    AlgHom.commutes,x1]

theorem x2_image : F (x2 A B) = s^2 * x2 C D := by
  change F (algebraMap (PairRing A B) (ChordRing A B) (rightPair A B (x A B))) = _
  simp only [chordHom_map,inputs_right,SelectedShortAffineScaling318.hom_x,map_mul,map_pow,
    AlgHom.commutes,x2]

theorem y1_image : F (y1 A B) = s^3 * y1 C D := by
  change F (algebraMap (PairRing A B) (ChordRing A B) (leftPair A B (y A B))) = _
  simp only [chordHom_map,inputs_left,SelectedShortAffineScaling318.hom_y,map_mul,map_pow,
    AlgHom.commutes,y1]

theorem y2_image : F (y2 A B) = s^3 * y2 C D := by
  change F (algebraMap (PairRing A B) (ChordRing A B) (rightPair A B (y A B))) = _
  simp only [chordHom_map,inputs_right,SelectedShortAffineScaling318.hom_y,map_mul,map_pow,
    AlgHom.commutes,y2]

theorem slope_image : F (slope A B) = s * slope C D := by
  have h := congrArg F (slope_identity A B)
  simp only [map_mul,map_sub,x1_image,x2_image,y1_image,y2_image] at h
  apply (((scale_isUnit C D r).pow 2).mul (gap_unit C D)).mul_right_cancel
  calc
    _ = s^3 * (y2 C D-y1 C D) := by linear_combination h
    _ = (s*slope C D) * (s^2*(x2 C D-x1 C D)) := by
      calc
        _ = s^3 * (slope C D * (x2 C D-x1 C D)) := by rw [slope_identity]
        _ = _ := by ring

theorem x3_image : F (x3 A B) = s^2*x3 C D := by
  simp only [x3,map_sub,map_pow,slope_image,x1_image,x2_image] <;> ring

theorem y3_image : F (y3 A B) = s^3*y3 C D := by
  simp only [y3,map_sub,map_mul,slope_image,x1_image,x3_image,y1_image] <;> ring

/-- Covariance of the ACTUAL addition on the selected secant open,
already at the level of algebra maps even over a nonreduced base. -/
theorem chord_pullback :
    F.comp (chordMap A B) = (chordMap C D).comp f := by
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,chordMap_x,SelectedShortAffineScaling318.hom_x,
      map_mul,map_pow,AlgHom.commutes,x3_image]
  · simp only [AlgHom.comp_apply,chordMap_y,SelectedShortAffineScaling318.hom_y,
      map_mul,map_pow,AlgHom.commutes,y3_image]

@[expose] def finiteMap : ShortAffineScheme318.scheme C D ⟶ ShortAffineScheme318.scheme A B :=
  Spec.map (CommRingCat.ofHom f.toRingHom)

@[expose] def secantMap : RelativeChordScheme318.chordOpen C D ⟶ RelativeChordScheme318.chordOpen A B :=
  Spec.map (CommRingCat.ofHom F.toRingHom)

theorem secant_addition :
    secantMap A B C D r hA hB ≫ RelativeChordScheme318.addition A B =
      RelativeChordScheme318.addition C D ≫ finiteMap A B C D r hA hB := by
  dsimp only [secantMap,finiteMap,RelativeChordScheme318.addition]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (chord_pullback A B C D r hA hB))

end SelectedSecantAdditionScaling318

#print axioms SelectedSecantAdditionScaling318.chord_pullback
#print axioms SelectedSecantAdditionScaling318.secant_addition
