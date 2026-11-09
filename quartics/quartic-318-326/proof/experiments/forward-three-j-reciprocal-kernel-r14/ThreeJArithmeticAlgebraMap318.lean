module
public import ThreeJModuliOpen318
public section
noncomputable section
namespace ThreeJArithmeticAlgebraMap318
open Polynomial ThreeJModuliOpen318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev A := OpenJAffineScheme318.A 3
abbrev B := OpenJAffineScheme318.B 3
abbrev XRing := ThreeTorsionAlgebra318.XRing A B
abbrev Fixed := LiteralThreeXComparison318.Fixed 3

lemma division_zero :
    (ThreeTorsionIdentity318.divisionPolynomial A B).eval₂ baseMap x=0 := by
  simp only [ThreeTorsionIdentity318.divisionPolynomial,eval₂_sub,eval₂_add,
    eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,eval₂_ofNat,map_mul,map_pow,
    map_ofNat,base_A,base_B]
  linear_combination 3*root_relation

lemma polynomial_zero : (ShortThreeTorsion318.polynomial A B).eval₂ baseMap x=0 := by
  have h := congrArg (fun p : Polynomial (OpenJModel318.Base 3) =>
    p.eval₂ baseMap x) (ShortThreeTorsion318.scalar_identity A B)
  simp only [eval₂_mul,eval₂_ofNat,division_zero] at h
  have h3 : IsUnit (3:Ring) := by
    simpa only [map_ofNat] using
      (show IsUnit (3:ℚ) from isUnit_iff_ne_zero.mpr (by norm_num)).map
        (algebraMap ℚ Ring)
  exact h3.mul_right_eq_zero.mp h

/-- Pullback of the original third-division x-algebra, not an abstract
four-element labeling of its fibers. -/
@[expose] def xMap : XRing →+* Ring := AdjoinRoot.lift baseMap x polynomial_zero
lemma xMap_root : xMap (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B))=x :=
  AdjoinRoot.lift_root ..
lemma xMap_base (r : OpenJModel318.Base 3) :
    xMap (algebraMap (OpenJModel318.Base 3) XRing r)=baseMap r := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.lift_of ..

/-- The actual full diamond-fixed algebra of the original primitive-three
cover. Its canonical sign quotient identifies it with the x-algebra. -/
@[expose] def fixedEquiv : XRing ≃ₐ[OpenJModel318.Base 3] Fixed :=
  ThreeTorsionSignQuotient318.signQuotientEquiv A B
    (OpenJAffineScheme318.discriminant_unit 3)
@[expose] def fixedMap : Fixed →+* Ring := xMap.comp fixedEquiv.symm.toRingEquiv.toRingHom
lemma fixedMap_base (r : OpenJModel318.Base 3) :
    fixedMap (algebraMap (OpenJModel318.Base 3) Fixed r)=baseMap r := by
  change xMap (fixedEquiv.symm (algebraMap (OpenJModel318.Base 3) Fixed r))=_
  rw [AlgEquiv.commutes,xMap_base]
lemma fixedMap_j :
    fixedMap (algebraMap (OpenJModel318.Base 3) Fixed (OpenJModel318.jCoord 3))=j := by
  rw [fixedMap_base,base_j]
lemma fixedMap_x : fixedMap (ModularArithmeticCoordinates318.xGenerator 3)=x := by
  change xMap (fixedEquiv.symm (fixedEquiv
    (AdjoinRoot.root (ShortThreeTorsion318.polynomial A B))))=x
  rw [AlgEquiv.symm_apply_apply,xMap_root]

end ThreeJArithmeticAlgebraMap318
