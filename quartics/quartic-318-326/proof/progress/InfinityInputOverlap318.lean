module
public import InfinityInputFiniteOverlap318
public import TangentChordOverlap318
public section
noncomputable section
namespace InfinityInputOverlap318
open InfinityInputAlgebra318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def overlapDenominator (A B:R) : PairRing A B := denominator A B*v A B
abbrev OverlapRing (A B:R) := Localization.Away (overlapDenominator A B)
@[expose] def commonMap (A B:R) : PairRing A B →ₐ[R] OverlapRing A B :=
  IsScalarTower.toAlgHom R (PairRing A B) (OverlapRing A B)

theorem two_units (A B:R) : IsUnit (commonMap A B (denominator A B)) ∧ IsUnit (commonMap A B (v A B)) := by
  have hh : IsUnit (commonMap A B (overlapDenominator A B)) :=
    IsLocalization.Away.algebraMap_isUnit (S:=OverlapRing A B) (overlapDenominator A B)
  simpa only [overlapDenominator,map_mul,IsUnit.mul_iff] using hh

@[expose] def fromInput (A B:R) : OutputRing A B →ₐ[R] OverlapRing A B :=
  IsLocalization.Away.liftAlgHom (f:=commonMap A B) (denominator A B) (two_units A B).1
@[simp] theorem fromInput_pair (A B:R) (a:PairRing A B) : fromInput A B (pairMap A B a)=commonMap A B a := by
  simp [fromInput,pairMap,IsLocalization.Away.liftAlgHom_apply]

@[expose] def firstInfinity (A B:R) : InfinityChart318.Ring A B →ₐ[R] OverlapRing A B :=
  (commonMap A B).comp (left A B)
@[expose] def firstOverlap (A B:R) : WeierstrassOverlap318.InfinityOverlap A B →ₐ[R] OverlapRing A B :=
  IsLocalization.Away.liftAlgHom (f:=firstInfinity A B) (InfinityChart318.z A B) (two_units A B).2
@[simp] theorem firstOverlap_integral (A B:R) (a:InfinityChart318.Ring A B) :
    firstOverlap A B (algebraMap (InfinityChart318.Ring A B) (WeierstrassOverlap318.InfinityOverlap A B) a)=firstInfinity A B a := by
  simp [firstOverlap,IsLocalization.Away.liftAlgHom_apply]
@[expose] def firstFinite (A B:R) : ShortAffineJacobian318.Ring A B →ₐ[R] OverlapRing A B :=
  (firstOverlap A B).comp (WeierstrassOverlap318.toInfinityBase A B)
@[expose] def secondFinite (A B:R) : ShortAffineJacobian318.Ring A B →ₐ[R] OverlapRing A B :=
  (commonMap A B).comp (right A B)

theorem first_y_relation (A B:R) : firstFinite A B (ShortAffineJacobian318.y A B)*commonMap A B (v A B)=1 := by
  have hh:=congrArg (firstOverlap A B) (WeierstrassOverlap318.iz_ii A B)
  simp only [map_mul,map_one,WeierstrassOverlap318.iz,firstOverlap_integral] at hh
  simp only [firstFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y]
  change _*firstInfinity A B (InfinityChart318.z A B)=1
  rw [mul_comm]
  exact hh

theorem first_x_relation (A B:R) : firstFinite A B (ShortAffineJacobian318.x A B)*commonMap A B (v A B)=commonMap A B (u A B) := by
  simp only [firstFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_x,map_mul,
    WeierstrassOverlap318.ix,firstOverlap_integral]
  have hh:=first_y_relation A B
  simp only [firstFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y] at hh
  rw [mul_assoc,hh,mul_one]
  rfl

@[expose] def finitePair (A B:R) : RelativeChordAlgebra318.PairRing A B →ₐ[R] OverlapRing A B :=
  Algebra.TensorProduct.lift (firstFinite A B) (secondFinite A B) (fun _ _ => Commute.all _ _)
@[simp] theorem finitePair_left (A B:R) (a:ShortAffineJacobian318.Ring A B) :
    finitePair A B (RelativeChordAlgebra318.leftPair A B a)=firstFinite A B a := by
  simp [finitePair,RelativeChordAlgebra318.leftPair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]
@[simp] theorem finitePair_right (A B:R) (a:ShortAffineJacobian318.Ring A B) :
    finitePair A B (RelativeChordAlgebra318.rightPair A B a)=secondFinite A B a := by
  simp [finitePair,RelativeChordAlgebra318.rightPair,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]

theorem chord_gap_unit (A B:R) : IsUnit (finitePair A B (RelativeChordAlgebra318.gap A B)) := by
  have hG:=congrArg (commonMap A B) (left_relation A B)
  have hm (a:PairRing A B) (n:ℕ) : commonMap A B (a^n)=(commonMap A B a)^n := by
    induction n with
    | zero =>
        simp only [pow_zero]
        change algebraMap (PairRing A B) (OverlapRing A B) 1=1
        exact (algebraMap (PairRing A B) (OverlapRing A B)).map_one
    | succ n ih => simp only [pow_succ,map_mul,ih]
  have h1 : commonMap A B 1=1 := by
    change algebraMap (PairRing A B) (OverlapRing A B) 1=1
    exact (algebraMap (PairRing A B) (OverlapRing A B)).map_one
  simp only [map_sub,map_mul,hm,map_zero,coeff,Algebra.ofId_apply,AlgHom.commutes] at hG
  have hH : IsUnit (InfinityInputPolynomial318.denominator
      (1-algebraMap R (OverlapRing A B) A*commonMap A B (u A B)*commonMap A B (v A B)-
        algebraMap R (OverlapRing A B) B*commonMap A B (v A B)^2)
      (commonMap A B (u A B)) (commonMap A B (x A B))) := by
    have hh:=(two_units A B).1
    simpa only [denominator,parameter,InfinityInputPolynomial318.denominator,map_sub,map_mul,
      hm,h1,coeff,Algebra.ofId_apply,AlgHom.commutes] using hh
  have hd:=InfinityInputFractions318.chord_denominator_unit _ _ _ _ _ hG (two_units A B).2 hH
  have he : finitePair A B (RelativeChordAlgebra318.gap A B)*commonMap A B (v A B)=
      commonMap A B (x A B)*commonMap A B (v A B)-commonMap A B (u A B) := by
    simp only [RelativeChordAlgebra318.gap,map_sub,finitePair_left,finitePair_right]
    rw [sub_mul,first_x_relation]
    rfl
  exact (IsUnit.mul_iff.mp (he.symm ▸ hd)).1

@[expose] def fromChord (A B:R) : RelativeChordAlgebra318.ChordRing A B →ₐ[R] OverlapRing A B :=
  IsLocalization.Away.liftAlgHom (f:=finitePair A B) (RelativeChordAlgebra318.gap A B) (chord_gap_unit A B)
@[simp] theorem fromChord_pair (A B:R) (a:RelativeChordAlgebra318.PairRing A B) :
    fromChord A B (TangentChordOverlap318.chordPairMap A B a)=finitePair A B a := by
  simp [fromChord,TangentChordOverlap318.chordPairMap,IsLocalization.Away.liftAlgHom_apply]

end InfinityInputOverlap318
