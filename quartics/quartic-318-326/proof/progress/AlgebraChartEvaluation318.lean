module
public import ChartInputEquality318
public import WholeBothNaturality318
public section
noncomputable section
namespace AlgebraChartEvaluation318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
abbrev F (A B:R) := ShortAffineJacobian318.Ring A B
abbrev I (A B:R) := InfinityChart318.Ring A B
@[expose] def pair {T U:Type u} [CommRing T] [CommRing U] [Algebra R T] [Algebra R U]
    (f:T →ₐ[R] S) (g:U →ₐ[R] S) : T ⊗[R] U →ₐ[R] S :=
  Algebra.TensorProduct.lift f g (fun _ _=>Commute.all _ _)
@[simp] theorem pair_left {T U:Type u} [CommRing T] [CommRing U] [Algebra R T] [Algebra R U]
    (f:T →ₐ[R] S) (g:U →ₐ[R] S) (t:T) :
    pair f g ((Algebra.TensorProduct.includeLeft : T →ₐ[R] T ⊗[R] U) t)=f t := by
  simp [pair,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]
@[simp] theorem pair_right {T U:Type u} [CommRing T] [CommRing U] [Algebra R T] [Algebra R U]
    (f:T →ₐ[R] S) (g:U →ₐ[R] S) (t:U) :
    pair f g ((Algebra.TensorProduct.includeRight : U →ₐ[R] T ⊗[R] U) t)=g t := by
  simp [pair,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]
@[expose] def finiteInput (A B:R) (f:F A B →ₐ[R] S) :
    Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WeierstrassGluing318.finiteChart A B
@[expose] def infinityInput (A B:R) (f:I A B →ₐ[R] S) :
    Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WeierstrassGluing318.infinityChart A B
@[expose] def finite (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (f g:F A B →ₐ[R] S) :
    Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom (pair f g).toRingHom) ≫ FiniteAdditionGluing318.coordinateAddition A B hD
@[expose] def mixed (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (f:I A B →ₐ[R] S) (g:F A B →ₐ[R] S) :
    Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom (pair f g).toRingHom) ≫ MixedAdditionGluing318.coordinateAddition A B hD
@[expose] def both (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) (f g:I A B →ₐ[R] S) :
    Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom (pair f g).toRingHom) ≫ WholeBothInfinity318.coordinateAddition A B hD

theorem finiteExtract_eq (A B:R) (f:I A B →ₐ[R] S) (g:F A B →ₐ[R] S)
    (h:infinityInput A B f=finiteInput A B g) (hv:IsUnit (f (InfinityChart318.z A B))) :
    InfinityExtraction318.finiteMap A B f hv=g := by
  apply ChartInputEquality318.finite_injective
  exact (InfinityExtraction318.input_agreement A B f hv).symm.trans h

theorem transition_unit (A B:R) (f:I A B →ₐ[R] S) (g:F A B →ₐ[R] S)
    (h:infinityInput A B f=finiteInput A B g) : IsUnit (f (InfinityChart318.z A B)) :=
  IsUnit.of_mul_eq_one (g (ShortAffineJacobian318.y A B))
    (ChartInputEquality318.finite_infinity A B g f h.symm).2

lemma mixed_first (A B:R) (f:I A B →ₐ[R] S) (g:F A B →ₐ[R] S) :
    MixedFiniteInput318.firstInfinity A B (pair f g)=f := by
  apply AlgHom.ext
  intro r
  exact pair_left f g r
lemma mixed_second (A B:R) (f:I A B →ₐ[R] S) (g:F A B →ₐ[R] S) :
    MixedFiniteInput318.secondFinite A B (pair f g)=g := by
  apply AlgHom.ext
  intro r
  exact pair_right f g r
lemma mixed_firstFinite (A B:R) (f:I A B →ₐ[R] S) (g:F A B →ₐ[R] S)
    (hv:IsUnit (f (InfinityChart318.z A B))) :
    MixedFiniteInput318.firstFinite A B (pair f g) (by simpa only [InfinityInputAlgebra318.v,InfinityInputAlgebra318.left,pair_left] using hv)=
      InfinityExtraction318.finiteMap A B f hv := by
  change InfinityExtraction318.finiteMap A B (MixedFiniteInput318.firstInfinity A B (pair f g)) _=_
  simp only [mixed_first]
lemma mixed_extract (A B:R) (f:I A B →ₐ[R] S) (g k:F A B →ₐ[R] S)
    (h:infinityInput A B f=finiteInput A B k) :
    MixedFiniteInput318.finitePair A B (pair f g)
      (by simpa only [InfinityInputAlgebra318.v,InfinityInputAlgebra318.left,pair_left] using transition_unit A B f k h)=
      pair k g := by
  change pair (MixedFiniteInput318.firstFinite A B (pair f g) _)
    (MixedFiniteInput318.secondFinite A B (pair f g))=pair k g
  rw [mixed_firstFinite A B f g (transition_unit A B f k h),mixed_second,finiteExtract_eq A B f k h (transition_unit A B f k h)]

theorem mixed_to_finite (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f:I A B →ₐ[R] S) (g k:F A B →ₐ[R] S) (h:infinityInput A B f=finiteInput A B k) :
    mixed A B hD f g=finite A B hD k g := by
  have hu:=transition_unit A B f k h
  have hv:IsUnit (pair f g (InfinityInputAlgebra318.v A B)) := by
    simpa only [InfinityInputAlgebra318.v,InfinityInputAlgebra318.left,pair_left] using hu
  unfold mixed finite
  rw [MixedAdditionNaturality318.finite_restriction A B hD (pair f g) hv,mixed_extract A B f g k h]
end AlgebraChartEvaluation318
