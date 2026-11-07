module
public import HomogeneousCross318
public import InfinityAdditionFinite318
public section
noncomputable section
namespace InfinityCrossMaps318
open InfinityAdditionAlgebra318 InfinityAdditionScheme318
open RelativeChordAlgebra318 (PairRing)
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Equality of the two actual infinity-output quotient maps on every common coefficient
algebra with the same pair input. This includes the inverse locus, not just a dense finite open. -/
theorem output_maps_agree (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (ψ:OutputRing A B true →ₐ[R] S)
    (hp:∀a:PairRing A B, φ (pairMap A B false a)=ψ (pairMap A B true a)) :
    φ.comp (outputMap A B false)=ψ.comp (outputMap A B true) := by
  let f:=φ.comp (pairMap A B false)
  have he (a:PairRing A B) : ψ (pairMap A B true a)=f a := (hp a).symm
  have hv (t:Bool) (q:OutputRing A B t →ₐ[R] S) :
      q (pairMap A B t (numeratorY A B t))*q (↑(numeratorYUnit A B t)⁻¹)=1 := by
    have hh:=congrArg q (Units.mul_inv (numeratorYUnit A B t))
    simpa only [map_mul,map_one,numeratorYUnit,IsUnit.unit_spec] using hh
  have hv0:=hv false φ
  have hv1:=hv true ψ
  rw [he] at hv1
  have hp':f (slopeNumerator A B false)*f (denominator A B true)-
      f (slopeNumerator A B true)*f (denominator A B false)=0 := by
    have hh:=congrArg f (HomogeneousCross318.actual_cross A B)
    simpa only [map_sub,map_mul,map_zero] using hh
  have hc : f (numeratorX A B false)*f (denominator A B false)*f (numeratorY A B true)=
      f (numeratorX A B true)*f (denominator A B true)*f (numeratorY A B false) ∧
      f (denominator A B false)^3*f (numeratorY A B true)=
        f (denominator A B true)^3*f (numeratorY A B false) := by
    have hh:=HomogeneousCross318.cross_coordinates (f (X1 A B)) (f (Y1 A B)) (f (X2 A B))
      (f (denominator A B false)) (f (slopeNumerator A B false))
      (f (denominator A B true)) (f (slopeNumerator A B true)) hp'
    simpa only [numeratorX,numeratorY,map_sub,InfinityAdditionFinite318.pair_pow,map_add,map_mul] using hh
  apply InfinityChart318.hom_ext
  · simp only [AlgHom.comp_apply,outputMap_x,outX,map_mul,he]
    exact HomogeneousCross318.inverse_cross _ _ _ _ _ _ hv0 hv1 hc.1
  · simp only [AlgHom.comp_apply,outputMap_z,outZ,map_mul,map_pow,he]
    exact HomogeneousCross318.inverse_cross _ _ _ _ _ _ hv0 hv1 hc.2

open AlgebraicGeometry CategoryTheory in
/-- Equality of the genuine Scheme maps, not merely a field-point identity. -/
theorem scheme_agreement (A B:R) (φ:OutputRing A B false →ₐ[R] S)
    (ψ:OutputRing A B true →ₐ[R] S)
    (hp:∀a:PairRing A B, φ (pairMap A B false a)=ψ (pairMap A B true a)) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ addition A B false=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ addition A B true := by
  dsimp only [addition,chartAddition]
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
  congr 2
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (output_maps_agree A B φ ψ hp))

end InfinityCrossMaps318
