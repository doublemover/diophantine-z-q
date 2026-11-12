module
public import WeierstrassGluing318
public section
noncomputable section
namespace WeierstrassActualChartComparison318
open AlgebraicGeometry CategoryTheory
open WeierstrassOverlap318
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (A B:R) (f:Affine A B→ₐ[R]S) (g:Infinity A B→ₐ[R]S)
  (hx:g (InfinityChart318.x A B)=f (ShortAffineJacobian318.x A B)*g (InfinityChart318.z A B))
  (hy:f (ShortAffineJacobian318.y A B)*g (InfinityChart318.z A B)=1)

/-- The actual two chart maps factor through the actual projective-cubic
overlap. No agreement only on points or generic fields is substituted. -/
@[expose] def overlap:InfinityOverlap A B→ₐ[R]S:=
  IsLocalization.Away.liftAlgHom (f:=g) (InfinityChart318.z A B)
    (IsUnit.of_mul_eq_one_right _ hy)

lemma overlap_on_infinity (a:Infinity A B):
    overlap A B f g hy (algebraMap (Infinity A B) (InfinityOverlap A B) a)=g a:=by
  simp only [overlap,IsLocalization.Away.liftAlgHom_apply]

lemma overlap_inverse:overlap A B f g hy (ii A B)=f (ShortAffineJacobian318.y A B):=by
  have h:=congrArg (overlap A B f g hy) (iz_ii A B)
  simp only [map_mul,map_one,iz,overlap_on_infinity] at h
  calc
    _=(f (ShortAffineJacobian318.y A B)*g (InfinityChart318.z A B))*
        overlap A B f g hy (ii A B):=by rw [hy,one_mul]
    _=f (ShortAffineJacobian318.y A B)*
        (g (InfinityChart318.z A B)*overlap A B f g hy (ii A B)):=by ring
    _=f (ShortAffineJacobian318.y A B):=by rw [h,mul_one]

include hx in
lemma finite_square:(overlap A B f g hy).comp (toInfinityBase A B)=f:=by
  apply affine_hom_ext
  · simp only [AlgHom.comp_apply,toInfinityBase_x,map_mul,ix,overlap_on_infinity,overlap_inverse]
    rw [hx]
    calc
      _=f (ShortAffineJacobian318.x A B)*
        (f (ShortAffineJacobian318.y A B)*g (InfinityChart318.z A B)):=by ring
      _=f (ShortAffineJacobian318.x A B):=by rw [hy,mul_one]
  · simp only [AlgHom.comp_apply,toInfinityBase_y,overlap_inverse]

/-- Exact equality after the genuine affine and infinity chart
inclusions into the independent proper Weierstrass scheme. -/
include hx hy in
theorem scheme_square:
    Spec.map (CommRingCat.ofHom f.toRingHom)≫WeierstrassGluing318.finiteChart A B=
    Spec.map (CommRingCat.ofHom g.toRingHom)≫WeierstrassGluing318.infinityChart A B:=by
  let e:=Spec.map (CommRingCat.ofHom (overlap A B f g hy).toRingHom)
  have hf:e≫WeierstrassGluing318.intoAffine A B=Spec.map (CommRingCat.ofHom f.toRingHom):=by
    rw [WeierstrassGluing318.intoAffine_eq]
    dsimp [e]
    rw [←Spec.map_comp]
    exact congrArg (fun h:Affine A B→ₐ[R]S=>Spec.map (CommRingCat.ofHom h.toRingHom))
      (finite_square A B f g hx hy)
  have hg:e≫WeierstrassGluing318.intoInfinity A B=Spec.map (CommRingCat.ofHom g.toRingHom):=by
    dsimp [e,WeierstrassGluing318.intoInfinity]
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact overlap_on_infinity A B f g hy
  rw [←hf,←hg,Category.assoc,Category.assoc]
  exact congrArg (fun h=>e≫h) (CategoryTheory.Limits.pushout.condition
    (f:=WeierstrassGluing318.intoAffine A B) (g:=WeierstrassGluing318.intoInfinity A B))
end WeierstrassActualChartComparison318
