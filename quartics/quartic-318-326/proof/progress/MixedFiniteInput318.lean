module
public import InfinityInputAlgebra318
public import WeierstrassOverlap318
public section
noncomputable section
namespace MixedFiniteInput318
open InfinityInputAlgebra318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Actual first finite input from the original infinity input whenever its z coordinate is a unit. -/
@[expose] def firstInfinity (A B:R) (f:PairRing A B →ₐ[R] S) : InfinityChart318.Ring A B →ₐ[R] S :=
  f.comp (left A B)
@[expose] def firstOverlap (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B))) :
    WeierstrassOverlap318.InfinityOverlap A B →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f:=firstInfinity A B f) (InfinityChart318.z A B) hv
@[simp] theorem firstOverlap_integral (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B)))
    (a:InfinityChart318.Ring A B) :
    firstOverlap A B f hv (algebraMap (InfinityChart318.Ring A B) (WeierstrassOverlap318.InfinityOverlap A B) a)=firstInfinity A B f a := by
  simp [firstOverlap,IsLocalization.Away.liftAlgHom_apply]
@[expose] def firstFinite (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B))) :
    ShortAffineJacobian318.Ring A B →ₐ[R] S :=
  (firstOverlap A B f hv).comp (WeierstrassOverlap318.toInfinityBase A B)
@[expose] def secondFinite (A B:R) (f:PairRing A B →ₐ[R] S) : ShortAffineJacobian318.Ring A B →ₐ[R] S := f.comp (right A B)

theorem first_y_relation (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B))) :
    firstFinite A B f hv (ShortAffineJacobian318.y A B)*f (v A B)=1 := by
  have hh:=congrArg (firstOverlap A B f hv) (WeierstrassOverlap318.iz_ii A B)
  simp only [map_mul,map_one,WeierstrassOverlap318.iz,firstOverlap_integral] at hh
  simp only [firstFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y]
  change _*firstInfinity A B f (InfinityChart318.z A B)=1
  rw [mul_comm]
  exact hh

theorem first_x_relation (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B))) :
    firstFinite A B f hv (ShortAffineJacobian318.x A B)*f (v A B)=f (u A B) := by
  simp only [firstFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_x,map_mul,
    WeierstrassOverlap318.ix,firstOverlap_integral]
  have hh:=first_y_relation A B f hv
  simp only [firstFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y] at hh
  rw [mul_assoc,hh,mul_one]
  rfl

/-- The actual transition coordinates uniquely determine the finite first input. -/
theorem firstFinite_unique (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B)))
    (g:ShortAffineJacobian318.Ring A B →ₐ[R] S)
    (hx:g (ShortAffineJacobian318.x A B)*f (v A B)=f (u A B))
    (hy:g (ShortAffineJacobian318.y A B)*f (v A B)=1) : g=firstFinite A B f hv := by
  apply AffineEquationFunctor318.hom_ext
  · exact hv.mul_right_cancel (hx.trans (first_x_relation A B f hv).symm)
  · exact hv.mul_right_cancel (hy.trans (first_y_relation A B f hv).symm)

@[expose] def finitePair (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B))) :
    RelativeChordAlgebra318.PairRing A B →ₐ[R] S :=
  Algebra.TensorProduct.lift (firstFinite A B f hv) (secondFinite A B f) (fun _ _ => Commute.all _ _)
@[simp] theorem finitePair_left (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B)))
    (a:ShortAffineJacobian318.Ring A B) :
    finitePair A B f hv (RelativeChordAlgebra318.leftPair A B a)=firstFinite A B f hv a := by
  simp [finitePair,RelativeChordAlgebra318.leftPair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]
@[simp] theorem finitePair_right (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B)))
    (a:ShortAffineJacobian318.Ring A B) :
    finitePair A B f hv (RelativeChordAlgebra318.rightPair A B a)=secondFinite A B f a := by
  simp [finitePair,RelativeChordAlgebra318.rightPair,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]

variable {T:Type u} [CommRing T] [Algebra R T]

/-- Actual finite-input extraction is natural under every coefficient-algebra map. -/
theorem firstFinite_natural (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B)))
    (g:S →ₐ[R] T) :
    g.comp (firstFinite A B f hv)=firstFinite A B (g.comp f) (hv.map g) := by
  apply firstFinite_unique
  · have hh:=congrArg g (first_x_relation A B f hv)
    simpa only [map_mul,AlgHom.comp_apply] using hh
  · have hh:=congrArg g (first_y_relation A B f hv)
    simpa only [map_mul,map_one,AlgHom.comp_apply] using hh

/-- The genuine tensor pair map is natural as well. -/
theorem finitePair_natural (A B:R) (f:PairRing A B →ₐ[R] S) (hv:IsUnit (f (v A B)))
    (g:S →ₐ[R] T) :
    g.comp (finitePair A B f hv)=finitePair A B (g.comp f) (hv.map g) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro a
    change g (finitePair A B f hv (RelativeChordAlgebra318.leftPair A B a))=
      finitePair A B (g.comp f) (hv.map g) (RelativeChordAlgebra318.leftPair A B a)
    rw [finitePair_left,finitePair_left]
    exact DFunLike.congr_fun (firstFinite_natural A B f hv g) a
  · apply AlgHom.ext
    intro a
    change g (finitePair A B f hv (RelativeChordAlgebra318.rightPair A B a))=
      finitePair A B (g.comp f) (hv.map g) (RelativeChordAlgebra318.rightPair A B a)
    rw [finitePair_right,finitePair_right]
    rfl

end MixedFiniteInput318
