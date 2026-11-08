module
public import IntrinsicAffineSectionEquiv318
public import IntrinsicGlobalFrame318
public section
noncomputable section
namespace WeierstrassAffineInvariant318
open AlgebraicGeometry CategoryTheory Opposite KaehlerDifferential
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R:Type u} [CommRing R] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))

@[expose] def finiteOpen := WeierstrassGluing318.finiteChart A B ''ᵁ ⊤
theorem finite_structure : WeierstrassGluing318.finiteChart A B ≫
    WeierstrassGluing318.structureMap A B=
      Spec.map (CommRingCat.ofHom (algebraMap R (ShortAffineJacobian318.Ring A B))) :=
  WeierstrassGluing318.finiteChart_structure A B

/-- The algebraic differential on the whole finite chart, obtained from the
actual invariant section through the exact intrinsic affine comparison. -/
@[expose] def form : KaehlerDifferential R (ShortAffineJacobian318.Ring A B) :=
  (IntrinsicAffineSectionEquiv318.equivalence (WeierstrassGluing318.finiteChart A B)
    (WeierstrassGluing318.structureMap A B) (finite_structure A B)).symm
      ((FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map (homOfLE le_top).op
        (IntrinsicGlobalFrame318.invariant A B hD))

theorem form_section :
    IntrinsicChartSections318.sectionMap (WeierstrassGluing318.finiteChart A B)
      (WeierstrassGluing318.structureMap A B) (finite_structure A B) (form A B hD)=
      (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map (homOfLE le_top).op
        (IntrinsicGlobalFrame318.invariant A B hD) :=
  (IntrinsicAffineSectionEquiv318.equivalence _ _ _).apply_symm_apply _

@[expose] def chartMap (i:Fin 2) : ShortAffineJacobian318.Ring A B →ₐ[R]
    WeierstrassKaehler318.AffineChart A B i := IsScalarTower.toAlgHom _ _ _

theorem form_local (i:Fin 2) (ω:KaehlerDifferential R (WeierstrassKaehler318.AffineChart A B i))
    (hω:(FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map (homOfLE le_top).op
      (IntrinsicGlobalFrame318.invariant A B hD)=
      IntrinsicChartSections318.sectionMap (InvariantChartCover318.finiteInto A B i)
        (WeierstrassGluing318.structureMap A B) (IntrinsicFamilyFrames318.finite_structure A B i) ω) :
    AlgHomDifferential318.map (chartMap A B i) (form A B hD)=ω := by
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective
    (InvariantChartCover318.finiteInto A B i) (WeierstrassGluing318.structureMap A B)
      (IntrinsicFamilyFrames318.finite_structure A B i)).1
  let k:=Spec.map (CommRingCat.ofHom (algebraMap (ShortAffineJacobian318.Ring A B)
    (WeierstrassKaehler318.AffineChart A B i)))
  let j:=WeierstrassGluing318.finiteChart A B
  letI:IsOpenImmersion k:=IsOpenImmersion.of_isLocalization (ShortAffineJacobian318.presentation A B i).jacobian
  letI:IsOpenImmersion (Spec.map (CommRingCat.ofHom (chartMap A B i).toRingHom)):=by
    change IsOpenImmersion k
    infer_instance
  have hn:=IntrinsicChartNaturality318.section_restrict (chartMap A B i) j
    (WeierstrassGluing318.structureMap A B) (finite_structure A B)
      (IntrinsicFamilyFrames318.finite_structure A B i) (form A B hD)
  rw [form_section] at hn
  have hc:=CategoryTheory.Functor.map_comp_apply
    (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf
    (homOfLE (show j ''ᵁ ⊤≤⊤ from le_top)).op
    (homOfLE (OpenChartSections318.imageLE k j)).op (IntrinsicGlobalFrame318.invariant A B hD)
  exact hn.symm.trans (hc.symm.trans hω)

theorem form_x : AlgHomDifferential318.map (chartMap A B 0) (form A B hD)=
    FiniteInvariantDifferential318.xForm A B :=
  form_local A B hD 0 _ (IntrinsicGlobalFrame318.invariant_restrict A B hD ⟨.x⟩)

theorem form_y : AlgHomDifferential318.map (chartMap A B 1) (form A B hD)=
    InvariantChartForms318.finite A B :=
  form_local A B hD 1 _ (IntrinsicGlobalFrame318.invariant_restrict A B hD ⟨.finite⟩)
end WeierstrassAffineInvariant318
