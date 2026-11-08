module
public import BothMixedFractions318
public import BothInfinityScheme318
public import InfinityInputScheme318
public import InfinityFiniteCompatibility318
public section
noncomputable section
namespace BothMixedMaps318
open BothInfinityAlgebra318 InfinityVietaAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma outU_relation (A B:R) :
    c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B)*
      (outU A B-u1 A B-u2 A B)=
      d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B) (intercept A B) := by
  have hu := Units.mul_inv (cubicUnit A B)
  have hval : (↑(cubicUnit A B) : OutputRing A B)=
      c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B) :=
    (cubic_coefficient_unit A B).unit_spec
  rw [hval] at hu
  rw [outU]
  linear_combination d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B)
    (slope A B) (intercept A B)*hu

/-- The actual regular both-infinity and mixed-input output coordinates agree under the
literal input-chart transition, over every coefficient algebra. -/
theorem coordinates (A B:R) (φ:OutputRing A B →ₐ[R] S)
    (ψ:InfinityInputAlgebra318.OutputRing A B →ₐ[R] S)
    (hu:φ (u1 A B)=ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.u A B)))
    (hv:φ (v1 A B)=ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.v A B)))
    (hx:φ (u2 A B)*ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.y A B))=
      ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.x A B)))
    (hy:φ (v2 A B)*ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.y A B))=1) :
    φ (outU A B)*ψ (InfinityInputAlgebra318.outY A B)=ψ (InfinityInputAlgebra318.outX A B) ∧
    φ (outV A B)*ψ (InfinityInputAlgebra318.outY A B)=1 := by
  let f:=ψ.comp (InfinityInputAlgebra318.pairMap A B)
  let a:=φ (slope A B)
  let b:=φ (intercept A B)
  have hfm (r:InfinityInputAlgebra318.PairRing A B) (n:ℕ) : f (r^n)=(f r)^n :=
    f.toRingHom.map_pow r n
  have hφm (r:OutputRing A B) (n:ℕ) : φ (r^n)=(φ r)^n := φ.toRingHom.map_pow r n
  have hf1:f 1=1:=f.toRingHom.map_one
  have hφ1:φ 1=1:=φ.toRingHom.map_one
  have hf2:f 2=2:=map_natCast f.toRingHom 2
  have hf3:f 3=3:=map_natCast f.toRingHom 3
  have hf4:f 4=4:=map_natCast f.toRingHom 4
  have hF:=congrArg f (InfinityInputAlgebra318.right_relation A B)
  have hG:=congrArg f (InfinityInputAlgebra318.left_relation A B)
  simp only [map_sub,map_mul,hfm,map_zero,InfinityInputAlgebra318.coeff,
    Algebra.ofId_apply,AlgHom.commutes] at hF hG
  have hl:=congrArg φ (line_first A B)
  simp only [map_add,map_mul,hu,hv] at hl
  have hm:=congrArg φ (line_second A B)
  simp only [map_add,map_mul] at hm
  have hM:1-a*f (InfinityInputAlgebra318.x A B)-b*f (InfinityInputAlgebra318.y A B)=0 := by
    change 1-φ (slope A B)*ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.x A B))-
      φ (intercept A B)*ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.y A B))=0
    rw [←hx]
    linear_combination ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.y A B))*hm-hy
  have hcmap:φ (c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B))=
      c (algebraMap R S A) (algebraMap R S B) a := by
    simp only [c,map_add,map_mul,hφm,hφ1,AlgHom.commutes,a]
  have hdmap:φ (d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B) (intercept A B))=
      d (algebraMap R S A) (algebraMap R S B) a b := by
    simp only [d,map_add,map_mul,hφm,map_ofNat,AlgHom.commutes,a,b]
  have hc:IsUnit (c (algebraMap R S A) (algebraMap R S B) a) := by
    rw [←hcmap]
    exact (cubic_coefficient_unit A B).map φ
  have hY:IsUnit (f (InfinityInputAlgebra318.y A B)) := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hy)
  have hU:=congrArg φ (outU_relation A B)
  simp only [map_mul,map_sub,hcmap,hdmap,hu] at hU
  have hU':c (algebraMap R S A) (algebraMap R S B) a*f (InfinityInputAlgebra318.y A B)*φ (outU A B)=
      (f (InfinityInputAlgebra318.u A B)*f (InfinityInputAlgebra318.y A B)+f (InfinityInputAlgebra318.x A B))*
        c (algebraMap R S A) (algebraMap R S B) a+
      d (algebraMap R S A) (algebraMap R S B) a b*f (InfinityInputAlgebra318.y A B) := by
    dsimp only [f,AlgHom.comp_apply]
    linear_combination ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.y A B))*hU+
      c (algebraMap R S A) (algebraMap R S B) a*hx
  have hV:φ (outV A B)=a*φ (outU A B)-b := by simp only [outV,map_sub,map_mul,a,b]
  have hH:f (InfinityInputAlgebra318.denominator A B)=
      InfinityInputPolynomial318.denominator
        (1-algebraMap R S A*f (InfinityInputAlgebra318.u A B)*f (InfinityInputAlgebra318.v A B)-
          algebraMap R S B*f (InfinityInputAlgebra318.v A B)^2)
        (f (InfinityInputAlgebra318.u A B)) (f (InfinityInputAlgebra318.x A B)) := by
    simp only [InfinityInputAlgebra318.denominator,InfinityInputPolynomial318.denominator,
      InfinityInputAlgebra318.parameter,map_sub,map_mul,hfm,hf1,InfinityInputAlgebra318.coeff,
      Algebra.ofId_apply,AlgHom.commutes]
  have hi:f (InfinityInputAlgebra318.denominator A B)*ψ (↑(InfinityInputAlgebra318.denominatorUnit A B)⁻¹)=1 := by
    have hh:=congrArg ψ (Units.mul_inv (InfinityInputAlgebra318.denominatorUnit A B))
    simpa only [map_mul,map_one,InfinityInputAlgebra318.denominatorUnit,IsUnit.unit_spec,
      f,AlgHom.comp_apply] using hh
  rw [hH] at hi
  have ht:=BothMixedFractions318.transition (algebraMap R S A) (algebraMap R S B)
    (f (InfinityInputAlgebra318.u A B)) (f (InfinityInputAlgebra318.v A B))
    (f (InfinityInputAlgebra318.x A B)) (f (InfinityInputAlgebra318.y A B))
    a b (φ (outU A B)) (φ (outV A B)) (ψ (↑(InfinityInputAlgebra318.denominatorUnit A B)⁻¹))
    hF hG (by dsimp only [f,a,b,AlgHom.comp_apply]; linear_combination hl) hM hc hY hU' hV hi
  simpa only [InfinityInputAlgebra318.outX,InfinityInputAlgebra318.outY,map_mul,map_pow,
    ←AlgHom.comp_apply,InfinityInputAlgebra318.numeratorX,InfinityInputAlgebra318.numeratorY,
    InfinityInputPolynomial318.numeratorX,InfinityInputPolynomial318.numeratorY,
    InfinityInputAlgebra318.parameter,map_add,map_sub,hfm,hf1,hf2,hf3,hf4,map_ofNat,
    InfinityInputAlgebra318.coeff,Algebra.ofId_apply,AlgHom.commutes,f,a,b] using ht

/-- The actual Scheme outputs agree under the same literal input transitions. -/
theorem scheme_agreement (A B:R) (φ:OutputRing A B →ₐ[R] S)
    (ψ:InfinityInputAlgebra318.OutputRing A B →ₐ[R] S)
    (hu:φ (u1 A B)=ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.u A B)))
    (hv:φ (v1 A B)=ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.v A B)))
    (hx:φ (u2 A B)*ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.y A B))=
      ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.x A B)))
    (hy:φ (v2 A B)*ψ (InfinityInputAlgebra318.pairMap A B (InfinityInputAlgebra318.y A B))=1) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ BothInfinityScheme318.addition A B=
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ InfinityInputScheme318.addition A B := by
  have ht:=coordinates A B φ ψ hu hv hx hy
  dsimp only [BothInfinityScheme318.addition,BothInfinityScheme318.chartAddition,
    InfinityInputScheme318.addition,InfinityInputScheme318.finiteAddition]
  rw [←Category.assoc,←Category.assoc,←Spec.map_comp,←Spec.map_comp]
  apply InfinityFiniteCompatibility318.scheme_agreement A B (φ.comp (outputMap A B))
    (ψ.comp (InfinityInputAlgebra318.outputMap A B))
  · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_x,
      InfinityInputAlgebra318.outputMap_x,InfinityInputAlgebra318.outputMap_y] using ht.1
  · simpa only [AlgHom.comp_apply,outputMap,InfinityChart318.lift_z,
      InfinityInputAlgebra318.outputMap_y] using ht.2

end BothMixedMaps318
