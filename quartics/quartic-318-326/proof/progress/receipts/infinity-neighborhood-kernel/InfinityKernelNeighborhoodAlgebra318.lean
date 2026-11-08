module
public import InfinityBoundaryDoubling318
public import InfinityKernelNeighborhoodOutput318
public section
noncomputable section
namespace InfinityKernelNeighborhoodAlgebra318
open BothInfinityAlgebra318
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

@[expose] def g (A B:R) := InfinityKernelNeighborhoodPolynomial318.G
  (algebraMap R (InfinityChart318.Ring A B) B) (InfinityChart318.z A B)
@[expose] def h (A B:R) := InfinityKernelNeighborhoodPolynomial318.H
  (algebraMap R (InfinityChart318.Ring A B) A) (algebraMap R (InfinityChart318.Ring A B) B)
  (InfinityChart318.x A B) (InfinityChart318.z A B)
@[expose] def diagonal (A B:R) : PairRing A B →ₐ[R] InfinityChart318.Ring A B :=
  InfinityBoundaryDoubling318.pairMap A B (AlgHom.id R _)
@[expose] def denominator (A B:R) := diagonal A B (domainElement A B)*g A B*h A B
abbrev Ring (A B:R) := Localization.Away (denominator A B)
@[expose] def input (A B:R) : InfinityChart318.Ring A B →ₐ[R] Ring A B :=
  IsScalarTower.toAlgHom R (InfinityChart318.Ring A B) (Ring A B)
@[expose] def pair (A B:R) : PairRing A B →ₐ[R] Ring A B := (input A B).comp (diagonal A B)
lemma pair_left (A B:R) (a:InfinityChart318.Ring A B) : pair A B (leftPair A B a)=input A B a := by
  simp only [pair,AlgHom.comp_apply,diagonal,InfinityBoundaryDoubling318.pair_left,AlgHom.id_apply]
lemma pair_right (A B:R) (a:InfinityChart318.Ring A B) : pair A B (rightPair A B a)=input A B a := by
  simp only [pair,AlgHom.comp_apply,diagonal,InfinityBoundaryDoubling318.pair_right,AlgHom.id_apply]
lemma unit_factors {U V:Type*} [CommRing U] [CommRing V] (f:U →+* V) (a b c:U)
    (hu:IsUnit (f (a*b*c))) : IsUnit (f a) ∧ IsUnit (f b) ∧ IsUnit (f c) := by
  rw [map_mul,map_mul] at hu
  exact ⟨isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu),
    isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu),isUnit_of_mul_isUnit_right hu⟩
lemma units (A B:R) : IsUnit (pair A B (domainElement A B)) ∧
    IsUnit (input A B (g A B)) ∧ IsUnit (input A B (h A B)) :=
  unit_factors (algebraMap (InfinityChart318.Ring A B) (Ring A B))
    (diagonal A B (domainElement A B)) (g A B) (h A B)
    (IsLocalization.Away.algebraMap_isUnit (S:=Ring A B) (denominator A B))
@[expose] def lift (A B:R) : OutputRing A B →ₐ[R] Ring A B :=
  IsLocalization.Away.liftAlgHom (f:=pair A B) (domainElement A B) (units A B).1
lemma lift_pair (A B:R) (a:PairRing A B) : lift A B (pairMap A B a)=pair A B a := by
  simp only [lift,pairMap,IsLocalization.Away.liftAlgHom_apply,IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl
lemma lift_u1 (A B:R) : lift A B (u1 A B)=input A B (InfinityChart318.x A B) := by
  rw [u1,lift_pair,U1,pair_left]
lemma lift_u2 (A B:R) : lift A B (u2 A B)=input A B (InfinityChart318.x A B) := by
  rw [u2,lift_pair,U2,pair_right]
lemma lift_v1 (A B:R) : lift A B (v1 A B)=input A B (InfinityChart318.z A B) := by
  rw [v1,lift_pair,V1,pair_left]
lemma lift_v2 (A B:R) : lift A B (v2 A B)=input A B (InfinityChart318.z A B) := by
  rw [v2,lift_pair,V2,pair_right]

lemma mapped_g (A B:R) : input A B (g A B)=InfinityKernelNeighborhoodPolynomial318.G
    (algebraMap R (Ring A B) B) (input A B (InfinityChart318.z A B)) := by
  simp only [g,InfinityKernelNeighborhoodPolynomial318.G,map_sub,map_one,map_mul,map_pow,AlgHom.commutes]
lemma mapped_h (A B:R) : input A B (h A B)=InfinityKernelNeighborhoodPolynomial318.H
    (algebraMap R (Ring A B) A) (algebraMap R (Ring A B) B)
    (input A B (InfinityChart318.x A B)) (input A B (InfinityChart318.z A B)) := by
  simp only [h,InfinityKernelNeighborhoodPolynomial318.H,InfinityKernelNeighborhoodPolynomial318.G,
    InfinityKernelNeighborhoodPolynomial318.C,InfinityKernelNeighborhoodPolynomial318.K,
    InfinityKernelNeighborhoodPolynomial318.Q,InfinityKernelNeighborhoodPolynomial318.S,
    InfinityVietaAlgebra318.q,InfinityVietaAlgebra318.s,
    map_sub,map_one,map_add,map_mul,map_pow,map_ofNat,AlgHom.commutes]

/-- The exact neighborhood eliminates all infinitesimal kernel directions
on every test ring. The asserted coordinate equality is an actual output. -/
theorem input_zero {T:Type*} [CommRing T] (A B:R) (φ:Ring A B →+* T)
    (ho:φ (lift A B (outU A B))=-φ (input A B (InfinityChart318.x A B))) :
    φ (input A B (InfinityChart318.x A B))=0 ∧ φ (input A B (InfinityChart318.z A B))=0 := by
  have hg:IsUnit (InfinityKernelNeighborhoodPolynomial318.G
      (φ (algebraMap R (Ring A B) B)) (φ (input A B (InfinityChart318.z A B)))) := by
    have hh:=(units A B).2.1.map φ
    simpa only [mapped_g,InfinityKernelNeighborhoodPolynomial318.G,map_sub,map_one,map_mul,map_pow] using hh
  have hh:IsUnit (InfinityKernelNeighborhoodPolynomial318.H
      (φ (algebraMap R (Ring A B) A)) (φ (algebraMap R (Ring A B) B))
      (φ (input A B (InfinityChart318.x A B))) (φ (input A B (InfinityChart318.z A B)))) := by
    have hh:=(units A B).2.2.map φ
    simpa only [mapped_h,InfinityKernelNeighborhoodPolynomial318.H,InfinityKernelNeighborhoodPolynomial318.G,
      InfinityKernelNeighborhoodPolynomial318.C,InfinityKernelNeighborhoodPolynomial318.K,
      InfinityKernelNeighborhoodPolynomial318.Q,InfinityKernelNeighborhoodPolynomial318.S,
      InfinityVietaAlgebra318.q,InfinityVietaAlgebra318.s,
      map_sub,map_one,map_add,map_mul,map_pow,map_ofNat] using hh
  let ψ:OutputRing A B →+* T:=φ.comp (lift A B).toRingHom
  have hψu1:ψ (u1 A B)=φ (input A B (InfinityChart318.x A B)) := by
    change φ (lift A B (u1 A B))=_
    rw [lift_u1]
  have hψu2:ψ (u2 A B)=φ (input A B (InfinityChart318.x A B)) := by
    change φ (lift A B (u2 A B))=_
    rw [lift_u2]
  have hψv1:ψ (v1 A B)=φ (input A B (InfinityChart318.z A B)) := by
    change φ (lift A B (v1 A B))=_
    rw [lift_v1]
  have hψv2:ψ (v2 A B)=φ (input A B (InfinityChart318.z A B)) := by
    change φ (lift A B (v2 A B))=_
    rw [lift_v2]
  have hψc (r:R):ψ (algebraMap R (OutputRing A B) r)=φ (algebraMap R (Ring A B) r) := by
    change φ (lift A B (algebraMap R (OutputRing A B) r))=_
    rw [AlgHom.commutes]
  have hz:=InfinityKernelNeighborhoodOutput318.input_zero A B ψ
    (hψu2.trans hψu1.symm) (hψv2.trans hψv1.symm)
    (by rw [hψu1];exact ho)
    (by simpa only [hψc,hψv1] using hg)
    (by simpa only [hψc,hψu1,hψv1] using hh)
  simpa only [hψu1,hψv1] using hz

end InfinityKernelNeighborhoodAlgebra318
