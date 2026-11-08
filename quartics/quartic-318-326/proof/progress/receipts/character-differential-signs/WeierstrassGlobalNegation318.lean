module
public import WeierstrassInvariantNegation318
public section
noncomputable section
namespace WeierstrassGlobalNegation318
open AlgebraicGeometry CategoryTheory Opposite KaehlerDifferential
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
universe u
variable {R:Type u} [CommRing R] [IsDomain R] (A B:R)
  (hD:IsUnit (-16*(4*A^3+27*B^2)))
  (hy:(2:ShortAffineJacobian318.Ring A B)*ShortAffineJacobian318.y A B≠0)
include hy
/-- The canonical intrinsic differential pullback by the actual global
elliptic involution sends the specified invariant generator to its negative. -/
theorem global : IntrinsicDifferentialPullback318.globalSection
    (X:=WeierstrassGluing318.scheme A B) (Y:=WeierstrassGluing318.scheme A B)
    (R:=CommRingCat.of R)
    (GluedNegation318.negation A B) (WeierstrassGluing318.structureMap A B)
      (WeierstrassGluing318.structureMap A B) (GluedNegation318.negation_over_base A B)
        (IntrinsicGlobalFrame318.invariant A B hD)= -IntrinsicGlobalFrame318.invariant A B hD:=by
  let p:=WeierstrassGluing318.structureMap A B
  let j:Spec (CommRingCat.of (ShortAffineJacobian318.Ring A B))⟶
      WeierstrassGluing318.scheme A B:=WeierstrassGluing318.finiteChart A B
  let a:ShortAffineJacobian318.Ring A B→ₐ[R]ShortAffineJacobian318.Ring A B:=
    ChartNegation318.affineNeg A B
  let f:=GluedNegation318.negation A B
  have hs:j≫f=Spec.map (CommRingCat.ofHom a.toRingHom)≫j:=
    GluedNegation318.finiteChart_negation A B
  have hv:j ''ᵁ ⊤≤f ⁻¹ᵁ (j ''ᵁ ⊤):=AffineChartPullbackScalars318.image_le _ _ _ _ hs
  have hn:=DFunLike.congr_fun
    (IntrinsicDifferentialSectionPullback318.sectionMap_naturality f p p
      (GluedNegation318.negation_over_base A B) a j j
        (WeierstrassAffineInvariant318.finite_structure A B)
        (WeierstrassAffineInvariant318.finite_structure A B) hs hv)
    (WeierstrassAffineInvariant318.form A B hD)
  simp only [AddMonoidHom.comp_apply] at hn
  rw [WeierstrassAffineInvariant318.form_section] at hn
  have hr:=IntrinsicDifferentialSectionPullback318.globalSection_restrict f p p
    (GluedNegation318.negation_over_base A B) (j ''ᵁ ⊤) (j ''ᵁ ⊤) hv
      (IntrinsicGlobalFrame318.invariant A B hD)
  have ha:=congrArg (IntrinsicChartSections318.sectionMap j p
    (WeierstrassAffineInvariant318.finite_structure A B))
      (WeierstrassInvariantNegation318.affine A B hD hy)
  have hneg:IntrinsicChartSections318.sectionMap j p
      (WeierstrassAffineInvariant318.finite_structure A B)
        (-WeierstrassAffineInvariant318.form A B hD)=
      -(FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map (homOfLE le_top).op
        (IntrinsicGlobalFrame318.invariant A B hD):=by
    exact (map_neg (IntrinsicChartSections318.sectionMap j p
      (WeierstrassAffineInvariant318.finite_structure A B)) _).trans
        (congrArg Neg.neg (WeierstrassAffineInvariant318.form_section A B hD))
  apply WeierstrassAffineFormCancellation318.restrict_injective A B hD
  exact (hr.symm.trans (hn.trans (ha.trans hneg))).trans
    (map_neg ((FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map
      (homOfLE (show WeierstrassAffineInvariant318.finiteOpen A B≤⊤ from le_top)).op).hom
        (IntrinsicGlobalFrame318.invariant A B hD)).symm
end WeierstrassGlobalNegation318
