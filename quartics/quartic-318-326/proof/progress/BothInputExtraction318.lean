module
public import InfinityExtraction318
public import BothInfinityAlgebra318
public import MixedFiniteInput318
public section
noncomputable section
namespace BothInputExtraction318
open BothInfinityAlgebra318
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
@[expose] def firstInfinity (A B:R) (f:PairRing A B →ₐ[R] S) := f.comp (leftPair A B)
@[expose] def secondInfinity (A B:R) (f:PairRing A B →ₐ[R] S) := f.comp (rightPair A B)
@[expose] def secondFinite (A B:R) (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B))) :=
  InfinityExtraction318.finiteMap A B (secondInfinity A B f) h
@[expose] def mixedPair (A B:R) (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B))) :
    InfinityInputAlgebra318.PairRing A B →ₐ[R] S :=
  Algebra.TensorProduct.lift (firstInfinity A B f) (secondFinite A B f h) (fun _ _ => Commute.all _ _)
@[simp] theorem mixedPair_left (A B:R) (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B)))
    (r:InfinityChart318.Ring A B) :
    mixedPair A B f h (InfinityInputAlgebra318.left A B r)=firstInfinity A B f r := by
  simp [mixedPair,InfinityInputAlgebra318.left,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]
@[simp] theorem mixedPair_right (A B:R) (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B)))
    (r:ShortAffineJacobian318.Ring A B) :
    mixedPair A B f h (InfinityInputAlgebra318.right A B r)=secondFinite A B f h r := by
  simp [mixedPair,InfinityInputAlgebra318.right,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]
@[simp] theorem first_u (A B:R) (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B))) :
    mixedPair A B f h (InfinityInputAlgebra318.u A B)=f (U1 A B) := mixedPair_left A B f h _
@[simp] theorem first_v (A B:R) (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B))) :
    mixedPair A B f h (InfinityInputAlgebra318.v A B)=f (V1 A B) := mixedPair_left A B f h _
theorem second_y (A B:R) (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B))) :
    f (V2 A B)*mixedPair A B f h (InfinityInputAlgebra318.y A B)=1 := by
  rw [InfinityInputAlgebra318.y,mixedPair_right]
  exact InfinityExtraction318.y_relation A B (secondInfinity A B f) h
theorem second_x (A B:R) (f:PairRing A B →ₐ[R] S) (h:IsUnit (f (V2 A B))) :
    f (U2 A B)*mixedPair A B f h (InfinityInputAlgebra318.y A B)=
      mixedPair A B f h (InfinityInputAlgebra318.x A B) := by
  rw [InfinityInputAlgebra318.y,InfinityInputAlgebra318.x,mixedPair_right,mixedPair_right]
  exact InfinityExtraction318.x_relation A B (secondInfinity A B f) h

@[expose] def finitePair (A B:R) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) :=
  MixedFiniteInput318.finitePair A B (mixedPair A B f h2) (by rw [first_v]; exact h1)
@[simp] theorem finitePair_left (A B:R) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) (r:ShortAffineJacobian318.Ring A B) :
    finitePair A B f h1 h2 (RelativeChordAlgebra318.leftPair A B r)=
      MixedFiniteInput318.firstFinite A B (mixedPair A B f h2) (by rw [first_v]; exact h1) r := by
  exact MixedFiniteInput318.finitePair_left A B _ _ r
@[simp] theorem finitePair_right (A B:R) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) (r:ShortAffineJacobian318.Ring A B) :
    finitePair A B f h1 h2 (RelativeChordAlgebra318.rightPair A B r)=secondFinite A B f h2 r := by
  rw [finitePair,MixedFiniteInput318.finitePair_right]
  change mixedPair A B f h2 (InfinityInputAlgebra318.right A B r)=_
  exact mixedPair_right A B f h2 r

lemma finite_y1 (A B:R) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) :
    finitePair A B f h1 h2 (RelativeChordAlgebra318.leftPair A B (ShortAffineJacobian318.y A B))*f (V1 A B)=1 := by
  rw [finitePair_left,←first_v A B f h2]
  exact MixedFiniteInput318.first_y_relation A B _ _
lemma finite_x1 (A B:R) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) :
    finitePair A B f h1 h2 (RelativeChordAlgebra318.leftPair A B (ShortAffineJacobian318.x A B))*f (V1 A B)=f (U1 A B) := by
  rw [finitePair_left,←first_v A B f h2,←first_u A B f h2]
  exact MixedFiniteInput318.first_x_relation A B _ _
lemma finite_y2 (A B:R) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) :
    finitePair A B f h1 h2 (RelativeChordAlgebra318.rightPair A B (ShortAffineJacobian318.y A B))*f (V2 A B)=1 := by
  rw [finitePair_right,mul_comm]
  exact InfinityExtraction318.y_relation A B (secondInfinity A B f) h2
lemma finite_x2 (A B:R) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) :
    finitePair A B f h1 h2 (RelativeChordAlgebra318.rightPair A B (ShortAffineJacobian318.x A B))*f (V2 A B)=f (U2 A B) := by
  rw [finitePair_right]
  have hx:=InfinityExtraction318.x_relation A B (secondInfinity A B f) h2
  have hy:=InfinityExtraction318.y_relation A B (secondInfinity A B f) h2
  change f (U2 A B)*secondFinite A B f h2 (ShortAffineJacobian318.y A B)=
    secondFinite A B f h2 (ShortAffineJacobian318.x A B) at hx
  change f (V2 A B)*secondFinite A B f h2 (ShortAffineJacobian318.y A B)=1 at hy
  rw [←hx]
  calc
    _=f (U2 A B)*(f (V2 A B)*secondFinite A B f h2 (ShortAffineJacobian318.y A B)) := by ring
    _=_ := by rw [hy,mul_one]
theorem secondFinite_natural (A B:R) (f:PairRing A B →ₐ[R] S)
    (h:IsUnit (f (V2 A B))) (g:S →ₐ[R] T) :
    g.comp (secondFinite A B f h)=secondFinite A B (g.comp f) (h.map g) :=
  InfinityExtraction318.natural A B (secondInfinity A B f) h g

theorem mixedPair_natural (A B:R) (f:PairRing A B →ₐ[R] S)
    (h:IsUnit (f (V2 A B))) (g:S →ₐ[R] T) :
    g.comp (mixedPair A B f h)=mixedPair A B (g.comp f) (h.map g) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro r
    change g (mixedPair A B f h (InfinityInputAlgebra318.left A B r))=
      mixedPair A B (g.comp f) (h.map g) (InfinityInputAlgebra318.left A B r)
    rw [mixedPair_left,mixedPair_left]
    rfl
  · apply AlgHom.ext
    intro r
    change g (mixedPair A B f h (InfinityInputAlgebra318.right A B r))=
      mixedPair A B (g.comp f) (h.map g) (InfinityInputAlgebra318.right A B r)
    rw [mixedPair_right,mixedPair_right]
    exact DFunLike.congr_fun (secondFinite_natural A B f h g) r

theorem finitePair_natural (A B:R) (f:PairRing A B →ₐ[R] S)
    (h1:IsUnit (f (V1 A B))) (h2:IsUnit (f (V2 A B))) (g:S →ₐ[R] T) :
    g.comp (finitePair A B f h1 h2)=finitePair A B (g.comp f) (h1.map g) (h2.map g) := by
  unfold finitePair
  simp only [MixedFiniteInput318.finitePair_natural,mixedPair_natural]
end BothInputExtraction318
