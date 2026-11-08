module
public import FinitePairCoefficient318
public section
noncomputable section
namespace FiniteOutputCoefficient318
open FinitePairCoefficient318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S

lemma local_left (A B:R) (i:Fin 4) (x:ShortAffineJacobian318.Ring A B) :
    localMap (S:=S) A B i (FiniteAdditionLocal318.inputMap A B i (RelativeChordAlgebra318.leftPair A B x))=
      FiniteAdditionLocal318.inputMap (a A) (a B) i (RelativeChordAlgebra318.leftPair (a A) (a B) (AffineBaseChange318.coefficientMap (S:=S) A B x)) := by
  rw [localMap_base,pair_left]
lemma local_right (A B:R) (i:Fin 4) (x:ShortAffineJacobian318.Ring A B) :
    localMap (S:=S) A B i (FiniteAdditionLocal318.inputMap A B i (RelativeChordAlgebra318.rightPair A B x))=
      FiniteAdditionLocal318.inputMap (a A) (a B) i (RelativeChordAlgebra318.rightPair (a A) (a B) (AffineBaseChange318.coefficientMap (S:=S) A B x)) := by
  rw [localMap_base,pair_right]
lemma local_coeff (A B r:R) (i:Fin 4) :
    localMap (S:=S) A B i (algebraMap R _ r)=algebraMap S _ (a r) := by
  exact ((localMap (S:=S) A B i).commutes r).trans
    (IsScalarTower.algebraMap_apply R S (FiniteAdditionLocal318.LocalRing (a A) (a B) i) r)

section Chord
open RelativeChordAlgebra318
abbrev chord (A B:R) : ChordRing A B →ₐ[R] ChordRing (a A) (a B) := localMap (S:=S) A B 0
@[simp] lemma chord_x1 (A B:R) : chord (S:=S) A B (x1 A B)=x1 (a A) (a B) := by
  change localMap (S:=S) A B 0 (FiniteAdditionLocal318.inputMap A B 0 (leftPair A B (ShortAffineJacobian318.x A B)))=_
  rw [local_left,AffineBaseChange318.coefficientMap_x]
  rfl
@[simp] lemma chord_x2 (A B:R) : chord (S:=S) A B (x2 A B)=x2 (a A) (a B) := by
  change localMap (S:=S) A B 0 (FiniteAdditionLocal318.inputMap A B 0 (rightPair A B (ShortAffineJacobian318.x A B)))=_
  rw [local_right,AffineBaseChange318.coefficientMap_x]
  rfl
@[simp] lemma chord_y1 (A B:R) : chord (S:=S) A B (y1 A B)=y1 (a A) (a B) := by
  change localMap (S:=S) A B 0 (FiniteAdditionLocal318.inputMap A B 0 (leftPair A B (ShortAffineJacobian318.y A B)))=_
  rw [local_left,AffineBaseChange318.coefficientMap_y]
  rfl
@[simp] lemma chord_y2 (A B:R) : chord (S:=S) A B (y2 A B)=y2 (a A) (a B) := by
  change localMap (S:=S) A B 0 (FiniteAdditionLocal318.inputMap A B 0 (rightPair A B (ShortAffineJacobian318.y A B)))=_
  rw [local_right,AffineBaseChange318.coefficientMap_y]
  rfl
@[simp] lemma chord_slope (A B:R) : chord (S:=S) A B (slope A B)=slope (a A) (a B) := by
  have h:=congrArg (chord (S:=S) A B) (slope_identity A B)
  simp only [map_mul,map_sub,chord_x1,chord_x2,chord_y1,chord_y2] at h
  exact (gap_unit (a A) (a B)).mul_right_cancel (h.trans (slope_identity (a A) (a B)).symm)
theorem chord_output (A B:R) : (chord (S:=S) A B).comp (chordMap A B)=
    ((chordMap (a A) (a B)).restrictScalars R).comp (AffineBaseChange318.coefficientMap (S:=S) A B) := by
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,chordMap_x,AffineBaseChange318.coefficientMap_x,x3,map_sub,map_pow,chord_slope,chord_x1,chord_x2]
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,chordMap_y,AffineBaseChange318.coefficientMap_y,y3,x3,map_sub,map_mul,map_pow,chord_slope,chord_x1,chord_x2,chord_y1]
end Chord

section Tangent
open TangentOpenAlgebra318
abbrev tangent (A B:R) : TangentRing A B →ₐ[R] TangentRing (a A) (a B) := localMap (S:=S) A B 1
@[simp] lemma tangent_x1 (A B:R) : tangent (S:=S) A B (x1 A B)=x1 (a A) (a B) := by
  change localMap (S:=S) A B 1 (FiniteAdditionLocal318.inputMap A B 1 (RelativeChordAlgebra318.leftPair A B (ShortAffineJacobian318.x A B)))=_
  rw [local_left,AffineBaseChange318.coefficientMap_x]
  rfl
@[simp] lemma tangent_x2 (A B:R) : tangent (S:=S) A B (x2 A B)=x2 (a A) (a B) := by
  change localMap (S:=S) A B 1 (FiniteAdditionLocal318.inputMap A B 1 (RelativeChordAlgebra318.rightPair A B (ShortAffineJacobian318.x A B)))=_
  rw [local_right,AffineBaseChange318.coefficientMap_x]
  rfl
@[simp] lemma tangent_y1 (A B:R) : tangent (S:=S) A B (y1 A B)=y1 (a A) (a B) := by
  change localMap (S:=S) A B 1 (FiniteAdditionLocal318.inputMap A B 1 (RelativeChordAlgebra318.leftPair A B (ShortAffineJacobian318.y A B)))=_
  rw [local_left,AffineBaseChange318.coefficientMap_y]
  rfl
@[simp] lemma tangent_y2 (A B:R) : tangent (S:=S) A B (y2 A B)=y2 (a A) (a B) := by
  change localMap (S:=S) A B 1 (FiniteAdditionLocal318.inputMap A B 1 (RelativeChordAlgebra318.rightPair A B (ShortAffineJacobian318.y A B)))=_
  rw [local_right,AffineBaseChange318.coefficientMap_y]
  rfl
@[simp] lemma tangent_slope (A B:R) : tangent (S:=S) A B (slope A B)=slope (a A) (a B) := by
  have h:=congrArg (tangent (S:=S) A B) (slope_sum A B)
  simp only [map_mul,map_add,map_pow,tangent_x1,tangent_x2,tangent_y1,tangent_y2] at h
  rw [show tangent (S:=S) A B (algebraMap R _ A)=algebraMap S _ (a A) from local_coeff A B A 1] at h
  exact (sum_unit (a A) (a B)).mul_right_cancel (h.trans (slope_sum (a A) (a B)).symm)
theorem tangent_output (A B:R) : (tangent (S:=S) A B).comp (tangentMap A B)=
    ((tangentMap (a A) (a B)).restrictScalars R).comp (AffineBaseChange318.coefficientMap (S:=S) A B) := by
  apply AffineEquationFunctor318.hom_ext
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,tangentMap_x,AffineBaseChange318.coefficientMap_x,x3,map_sub,map_pow,tangent_slope,tangent_x1,tangent_x2]
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,tangentMap_y,AffineBaseChange318.coefficientMap_y,y3,x3,map_sub,map_mul,map_pow,tangent_slope,tangent_x1,tangent_x2,tangent_y1]
end Tangent
end FiniteOutputCoefficient318
