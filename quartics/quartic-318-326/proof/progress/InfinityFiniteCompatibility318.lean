module
public import InfinityAdditionScheme318
import all WeierstrassGluing318
public section
noncomputable section
namespace InfinityFiniteCompatibility318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassOverlap318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Actual finite/infinity Scheme maps agree whenever their literal projective coordinates agree.
This uses the genuine common localization and pushout, not agreement on field-valued points. -/
theorem scheme_agreement (A B:R) (ψ:Infinity A B →ₐ[R] S) (χ:Affine A B →ₐ[R] S)
    (hx:ψ (InfinityChart318.x A B)*χ (ShortAffineJacobian318.y A B)=χ (ShortAffineJacobian318.x A B))
    (hz:ψ (InfinityChart318.z A B)*χ (ShortAffineJacobian318.y A B)=1) :
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ WeierstrassGluing318.infinityChart A B=
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ WeierstrassGluing318.finiteChart A B := by
  have hu : IsUnit (ψ (InfinityChart318.z A B)):=IsUnit.of_mul_eq_one _ hz
  let e : InfinityOverlap A B →ₐ[R] S := IsLocalization.Away.liftAlgHom (f:=ψ)
    (InfinityChart318.z A B) hu
  have he (a:Infinity A B) : e (algebraMap (Infinity A B) (InfinityOverlap A B) a)=ψ a :=
    IsLocalization.Away.lift_eq _ hu a
  have hi : e (ii A B)=χ (ShortAffineJacobian318.y A B) := by
    apply hu.mul_left_cancel
    have hh:=congrArg e (iz_ii A B)
    simpa only [map_mul,map_one,iz,he,hz] using hh
  have hχ : e.comp (toInfinityBase A B)=χ := by
    apply affine_hom_ext
    · simpa only [AlgHom.comp_apply,toInfinityBase_x,map_mul,ix,he,hi] using hx
    · simp only [AlgHom.comp_apply,toInfinityBase_y,hi]
  have hψ : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ WeierstrassGluing318.intoInfinity A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
    dsimp only [WeierstrassGluing318.intoInfinity]
    rw [←Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext he)
  have hχ' : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ WeierstrassGluing318.intoAffine A B=
      Spec.map (CommRingCat.ofHom χ.toRingHom) := by
    rw [WeierstrassGluing318.intoAffine_eq]
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact DFunLike.congr_fun hχ a
  rw [←hψ,Category.assoc]
  change _ ≫ (WeierstrassGluing318.intoInfinity A B ≫ pushout.inr _ _)=_
  rw [←pushout.condition,←Category.assoc,hχ']
  rfl

open InfinityAdditionAlgebra318
/-- The actual homogeneous output and a finite output with the corresponding denominator-cleared
coordinates induce identical morphisms into the completed curve over every coefficient algebra. -/
theorem output_agreement (A B:R) (t:Bool) (φ:OutputRing A B t →ₐ[R] S)
    (χ:Affine A B →ₐ[R] S)
    (hd:IsUnit (φ (pairMap A B t (denominator A B t))))
    (hx:χ (ShortAffineJacobian318.x A B)*φ (pairMap A B t (denominator A B t))^2=
      φ (pairMap A B t (numeratorX A B t)))
    (hy:χ (ShortAffineJacobian318.y A B)*φ (pairMap A B t (denominator A B t))^3=
      φ (pairMap A B t (numeratorY A B t))) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ InfinityAdditionScheme318.addition A B t=
      Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ WeierstrassGluing318.finiteChart A B := by
  have hk : φ (pairMap A B t (numeratorY A B t))*φ (↑(numeratorYUnit A B t)⁻¹)=1 := by
    have hh:=congrArg φ (Units.mul_inv (numeratorYUnit A B t))
    simpa only [map_mul,map_one,numeratorYUnit,IsUnit.unit_spec] using hh
  have hz : (φ.comp (outputMap A B t)) (InfinityChart318.z A B)*χ (ShortAffineJacobian318.y A B)=1 := by
    simp only [AlgHom.comp_apply,outputMap_z,outZ,map_mul,map_pow]
    calc
      _=(χ (ShortAffineJacobian318.y A B)*φ (pairMap A B t (denominator A B t))^3)*φ (↑(numeratorYUnit A B t)⁻¹) := by ring
      _=1 := by rw [hy,hk]
  have hx' : (φ.comp (outputMap A B t)) (InfinityChart318.x A B)*χ (ShortAffineJacobian318.y A B)=χ (ShortAffineJacobian318.x A B) := by
    apply (hd.pow 2).mul_right_cancel
    simp only [AlgHom.comp_apply,outputMap_x,outX,map_mul]
    calc
      _=φ (pairMap A B t (numeratorX A B t)) *
        ((χ (ShortAffineJacobian318.y A B)*φ (pairMap A B t (denominator A B t))^3)*φ (↑(numeratorYUnit A B t)⁻¹)) := by ring
      _=χ (ShortAffineJacobian318.x A B)*φ (pairMap A B t (denominator A B t))^2 := by rw [hy,hk,mul_one,hx]
  dsimp only [InfinityAdditionScheme318.addition,InfinityAdditionScheme318.chartAddition]
  rw [←Category.assoc,←Spec.map_comp]
  exact scheme_agreement A B (φ.comp (outputMap A B t)) χ hx' hz

end InfinityFiniteCompatibility318
