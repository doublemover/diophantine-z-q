module
public import BothMixedMaps318
public import WeierstrassOverlap318
public section
noncomputable section
namespace BothMixedConcrete318
open BothInfinityAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]
@[expose] def mixedNumerator (A B:R) : PairRing A B :=
  (1-coeff A B A*U1 A B*V1 A B-coeff A B B*V1 A B^2)*V2 A B-U2 A B*U1 A B^2
@[expose] def overlapElement (A B:R) : PairRing A B :=
  domainElement A B*V2 A B*mixedNumerator A B
namespace Triple
variable {T : Type*} [CommRing T] [Algebra R T]
abbrev Ring (x y z:T) := Localization.Away (x*y*z)
@[expose] def map (x y z:T) : T →ₐ[R] Ring x y z :=
  IsScalarTower.toAlgHom R T (Ring x y z)
lemma units (x y z:T) : IsUnit (map (R:=R) x y z x) ∧
    IsUnit (map (R:=R) x y z y) ∧ IsUnit (map (R:=R) x y z z) := by
  have h : IsUnit (map (R:=R) x y z (x*y*z)) :=
    IsLocalization.Away.algebraMap_isUnit (S:=Ring x y z) (x*y*z)
  simpa only [map_mul,IsUnit.mul_iff,and_assoc] using h
instance map_open (x y z:T) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (map (R:=R) x y z).toRingHom)) :=
  IsOpenImmersion.of_isLocalization (S:=Ring x y z) (x*y*z)
@[expose] def intoScheme (x y z:T) {X : Scheme} (e : Spec (CommRingCat.of T) ≅ X) :
    Spec (CommRingCat.of (Ring x y z)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (map (R:=R) x y z).toRingHom) ≫ e.hom
instance intoScheme_open (x y z:T) {X : Scheme} (e : Spec (CommRingCat.of T) ≅ X) :
    IsOpenImmersion (intoScheme (R:=R) x y z e) := by
  dsimp only [intoScheme]
  infer_instance
end Triple
abbrev CommonRing (A B:R) := Triple.Ring (domainElement A B) (V2 A B) (mixedNumerator A B)
@[expose] def commonMap (A B:R) : PairRing A B →ₐ[R] CommonRing A B :=
  Triple.map (domainElement A B) (V2 A B) (mixedNumerator A B)
lemma three_units (A B:R) :
    IsUnit (commonMap A B (domainElement A B)) ∧ IsUnit (commonMap A B (V2 A B)) ∧
      IsUnit (commonMap A B (mixedNumerator A B)) :=
  Triple.units (domainElement A B) (V2 A B) (mixedNumerator A B)
@[expose] def fromBoth (A B:R) : OutputRing A B →ₐ[R] CommonRing A B :=
  IsLocalization.Away.liftAlgHom (f:=commonMap A B) (domainElement A B) (three_units A B).1
@[simp] lemma fromBoth_pair (A B:R) (r:PairRing A B) : fromBoth A B (pairMap A B r)=commonMap A B r := by
  simp only [fromBoth,pairMap,IsLocalization.Away.liftAlgHom_apply,
    IsScalarTower.toAlgHom_apply,IsLocalization.Away.lift_eq]
  rfl
@[expose] def firstInfinity (A B:R) : InfinityChart318.Ring A B →ₐ[R] CommonRing A B :=
  (commonMap A B).comp (leftPair A B)
@[expose] def secondInfinity (A B:R) : InfinityChart318.Ring A B →ₐ[R] CommonRing A B :=
  (commonMap A B).comp (rightPair A B)
@[expose] def secondOverlap (A B:R) : WeierstrassOverlap318.InfinityOverlap A B →ₐ[R] CommonRing A B :=
  IsLocalization.Away.liftAlgHom (f:=secondInfinity A B) (InfinityChart318.z A B) (three_units A B).2.1
@[simp] theorem secondOverlap_integral (A B:R) (r:InfinityChart318.Ring A B) :
    secondOverlap A B (algebraMap (InfinityChart318.Ring A B) (WeierstrassOverlap318.InfinityOverlap A B) r)=secondInfinity A B r := by
  simp [secondOverlap,IsLocalization.Away.liftAlgHom_apply]
@[expose] def secondFinite (A B:R) : ShortAffineJacobian318.Ring A B →ₐ[R] CommonRing A B :=
  (secondOverlap A B).comp (WeierstrassOverlap318.toInfinityBase A B)
theorem second_y_relation (A B:R) : secondFinite A B (ShortAffineJacobian318.y A B)*commonMap A B (V2 A B)=1 := by
  have hh:=congrArg (secondOverlap A B) (WeierstrassOverlap318.iz_ii A B)
  simp only [map_mul,map_one,WeierstrassOverlap318.iz,secondOverlap_integral] at hh
  simp only [secondFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y]
  change _ *secondInfinity A B (InfinityChart318.z A B)=1
  rw [mul_comm]
  exact hh
theorem second_x_relation (A B:R) : secondFinite A B (ShortAffineJacobian318.x A B)*commonMap A B (V2 A B)=commonMap A B (U2 A B) := by
  simp only [secondFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_x,map_mul,
    WeierstrassOverlap318.ix,secondOverlap_integral]
  have hh:=second_y_relation A B
  simp only [secondFinite,AlgHom.comp_apply,WeierstrassOverlap318.toInfinityBase_y] at hh
  rw [mul_assoc,hh,mul_one]
  rfl
@[expose] def mixedPair (A B:R) : InfinityInputAlgebra318.PairRing A B →ₐ[R] CommonRing A B :=
  Algebra.TensorProduct.lift (firstInfinity A B) (secondFinite A B) (fun _ _=>Commute.all _ _)
@[simp] lemma mixedPair_left (A B:R) (r:InfinityChart318.Ring A B) :
    mixedPair A B (InfinityInputAlgebra318.left A B r)=firstInfinity A B r := by
  simp [mixedPair,InfinityInputAlgebra318.left,Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.lift_tmul]
@[simp] lemma mixedPair_right (A B:R) (r:ShortAffineJacobian318.Ring A B) :
    mixedPair A B (InfinityInputAlgebra318.right A B r)=secondFinite A B r := by
  simp [mixedPair,InfinityInputAlgebra318.right,Algebra.TensorProduct.includeRight_apply,Algebra.TensorProduct.lift_tmul]
lemma mixed_denominator (A B:R) :
    mixedPair A B (InfinityInputAlgebra318.denominator A B)*commonMap A B (V2 A B)=
      commonMap A B (mixedNumerator A B) := by
  have hm (r:InfinityInputAlgebra318.PairRing A B) (n:ℕ) : mixedPair A B (r^n)=(mixedPair A B r)^n :=
    (mixedPair A B).toRingHom.map_pow r n
  have hc (r:PairRing A B) (n:ℕ) : commonMap A B (r^n)=(commonMap A B r)^n :=
    (commonMap A B).toRingHom.map_pow r n
  have h1:mixedPair A B 1=1:=(mixedPair A B).toRingHom.map_one
  have h2:commonMap A B 1=1:=(commonMap A B).toRingHom.map_one
  simp only [InfinityInputAlgebra318.denominator,InfinityInputPolynomial318.denominator,
    InfinityInputAlgebra318.parameter,mixedNumerator,map_sub,map_mul,hm,hc,h1,h2,
    InfinityInputAlgebra318.u,InfinityInputAlgebra318.v,InfinityInputAlgebra318.x,
    mixedPair_left,mixedPair_right,InfinityInputAlgebra318.coeff,coeff,Algebra.ofId_apply,AlgHom.commutes]
  change (1-algebraMap R (CommonRing A B) A*commonMap A B (U1 A B)*commonMap A B (V1 A B)-
      algebraMap R (CommonRing A B) B*commonMap A B (V1 A B)^2-
      secondFinite A B (ShortAffineJacobian318.x A B)*commonMap A B (U1 A B)^2)*commonMap A B (V2 A B)=_
  linear_combination -commonMap A B (U1 A B)^2*second_x_relation A B
lemma mixed_denominator_unit (A B:R) : IsUnit (mixedPair A B (InfinityInputAlgebra318.denominator A B)) := by
  apply isUnit_of_mul_isUnit_left (y:=commonMap A B (V2 A B))
  rw [mixed_denominator]
  exact (three_units A B).2.2
@[expose] def fromMixed (A B:R) : InfinityInputAlgebra318.OutputRing A B →ₐ[R] CommonRing A B :=
  IsLocalization.Away.liftAlgHom (f:=mixedPair A B) (InfinityInputAlgebra318.denominator A B)
    (mixed_denominator_unit A B)
@[simp] lemma fromMixed_pair (A B:R) (r:InfinityInputAlgebra318.PairRing A B) :
    fromMixed A B (InfinityInputAlgebra318.pairMap A B r)=mixedPair A B r := by
  simp [fromMixed,InfinityInputAlgebra318.pairMap,IsLocalization.Away.liftAlgHom_apply]

/-- All transition assumptions are discharged on this concrete principal overlap. -/
theorem output_agreement (A B:R) :
    Spec.map (CommRingCat.ofHom (fromBoth A B).toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom (fromMixed A B).toRingHom) ≫ InfinityInputScheme318.addition A B := by
  apply BothMixedMaps318.scheme_agreement
  · simp only [u1,fromBoth_pair,fromMixed_pair,InfinityInputAlgebra318.u,mixedPair_left]
    rfl
  · simp only [v1,fromBoth_pair,fromMixed_pair,InfinityInputAlgebra318.v,mixedPair_left]
    rfl
  · simp only [u2,fromBoth_pair,fromMixed_pair,InfinityInputAlgebra318.y,InfinityInputAlgebra318.x,mixedPair_right]
    apply (three_units A B).2.1.mul_right_cancel
    calc
      _=commonMap A B (U2 A B)*(secondFinite A B (ShortAffineJacobian318.y A B)*commonMap A B (V2 A B)) := by ring
      _=commonMap A B (U2 A B) := by rw [second_y_relation,mul_one]
      _=_ := (second_x_relation A B).symm
  · simp only [v2,fromBoth_pair,fromMixed_pair,InfinityInputAlgebra318.y,mixedPair_right]
    rw [mul_comm,second_y_relation]
/-- This is an actual principal open in the infinity-times-infinity input product. -/
@[expose] def intoProduct (A B:R) : Spec (CommRingCat.of (CommonRing A B)) ⟶ BothInfinityScheme318.productScheme A B :=
  Triple.intoScheme (R:=R) (domainElement A B) (V2 A B) (mixedNumerator A B)
    (pullbackSpecIso R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).symm
/-- The open-immersion witness for the displayed generic principal-open composite.
Its inferred type is definitionally the type of `intoProduct A B`. -/
@[expose] def intoProduct_open (A B:R) :=
  Triple.intoScheme_open (R:=R) (domainElement A B) (V2 A B) (mixedNumerator A B)
    (pullbackSpecIso R (InfinityChart318.Ring A B) (InfinityChart318.Ring A B)).symm

theorem into_both (A B:R) :
    Spec.map (CommRingCat.ofHom (fromBoth A B).toRingHom) ≫ BothInfinityScheme318.intoProduct A B=intoProduct A B := by
  dsimp only [BothInfinityScheme318.intoProduct,BothInfinityScheme318.domain,intoProduct,Triple.intoScheme,
    BothInfinityScheme318.productScheme,InfinitySmooth318.structureMap,InfinitySmooth318.scheme]
  rw [←Category.assoc,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (RingHom.ext (fromBoth_pair A B))

/-- The finite extraction of the second input preserves its actual point in the completed curve. -/
theorem second_input_agreement (A B:R) :
    Spec.map (CommRingCat.ofHom (secondInfinity A B).toRingHom) ≫ WeierstrassGluing318.infinityChart A B=
      Spec.map (CommRingCat.ofHom (secondFinite A B).toRingHom) ≫ WeierstrassGluing318.finiteChart A B := by
  apply InfinityFiniteCompatibility318.scheme_agreement
  · change commonMap A B (U2 A B)*secondFinite A B (ShortAffineJacobian318.y A B)=_
    apply (three_units A B).2.1.mul_right_cancel
    calc
      _=commonMap A B (U2 A B)*(secondFinite A B (ShortAffineJacobian318.y A B)*commonMap A B (V2 A B)) := by ring
      _=commonMap A B (U2 A B) := by rw [second_y_relation,mul_one]
      _=_ := (second_x_relation A B).symm
  · change commonMap A B (V2 A B)*secondFinite A B (ShortAffineJacobian318.y A B)=1
    rw [mul_comm,second_y_relation]

end BothMixedConcrete318
