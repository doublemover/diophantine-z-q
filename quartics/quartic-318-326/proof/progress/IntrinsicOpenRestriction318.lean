module
public import DerivationOpenRestriction318
public section
noncomputable section
namespace IntrinsicOpenRestriction318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  {R : CommRingCat.{u}} (φ : (Functor.const Y.Opensᵒᵖ).obj R ⟶ Y.presheaf)

@[expose] def D := DerivationOpenRestriction318.restrict j φ
  (UniversalSheafDifferentials318.D φ)

/-- Descend through intrinsic universality on the ambient scheme, then restrict
and apply the actual open-immersion adjunction counit. -/
@[expose] def desc {M : X.Modules}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (DerivationOpenRestriction318.coefficients j φ)) :
    (UniversalSheafDifferentials318.omega φ).restrict j ⟶ M :=
  (Scheme.Modules.restrictFunctor j).map
    (UniversalSheafDifferentials318.desc φ (DerivationOpenRestriction318.push j φ d)) ≫
      (Scheme.Modules.restrictAdjunction j).counit.app M

theorem desc_fac {M : X.Modules}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (DerivationOpenRestriction318.coefficients j φ)) :
    (D j φ).postcomp (desc j φ d).val = d := by
  ext U a
  let i := (eqToHom (j.preimage_image_eq U.unop).symm).op
  have hf := PresheafOfModulesOfCommRing.Derivation.congr_d
    (UniversalSheafDifferentials318.desc_fac φ (DerivationOpenRestriction318.push j φ d))
    (X:=op (j ''ᵁ U.unop)) ((j.appIso U.unop).inv a)
  have hi := congrArg (fun k => k a) (j.appIso_inv_app_presheafMap U.unop)
  change M.val.map i
    ((UniversalSheafDifferentials318.desc φ (DerivationOpenRestriction318.push j φ d)).val.app _
      ((UniversalSheafDifferentials318.D φ).d ((j.appIso U.unop).inv a)))=d.d a
  exact (congrArg (M.val.map i) hf).trans
    ((d.d_map i (j.app (j ''ᵁ U.unop) ((j.appIso U.unop).inv a))).symm.trans
      (congrArg (fun z => d.d (X:=U) z) hi))

/-- Maps out of the actual restricted intrinsic sheaf are determined by the
restricted universal derivation. -/
theorem hom_ext {M : X.Modules}
    {a b : (UniversalSheafDifferentials318.omega φ).restrict j ⟶ M}
    (h : (D j φ).postcomp a.val=(D j φ).postcomp b.val) : a=b := by
  apply ((Scheme.Modules.restrictAdjunction j).homEquiv _ _).injective
  apply UniversalSheafDifferentials318.hom_ext φ
  ext V x
  let U := j ⁻¹ᵁ V.unop
  let i := (homOfLE (j.image_preimage_le V.unop)).op
  have hh := PresheafOfModulesOfCommRing.Derivation.congr_d h (X:=op U) (j.app V.unop x)
  have hj := congrArg (fun k => k x) (j.app_appIso_inv V.unop)
  have hd := (UniversalSheafDifferentials318.D φ).d_map i x
  change a.val.app (op U)
      ((UniversalSheafDifferentials318.omega φ).val.map i ((UniversalSheafDifferentials318.D φ).d x)) =
    b.val.app (op U)
      ((UniversalSheafDifferentials318.omega φ).val.map i ((UniversalSheafDifferentials318.D φ).d x))
  change a.val.app (op U) ((UniversalSheafDifferentials318.D φ).d
      ((j.appIso U).inv (j.app V.unop x))) =
    b.val.app (op U) ((UniversalSheafDifferentials318.D φ).d
      ((j.appIso U).inv (j.app V.unop x))) at hh
  have ht := (congrArg (fun z => (UniversalSheafDifferentials318.D φ).d
    (X:=op (j ''ᵁ U)) z) hj).trans hd
  exact (congrArg (a.val.app (op U)) ht).symm.trans
    (hh.trans (congrArg (b.val.app (op U)) ht))

theorem isUniversal : IntrinsicUniversalComparison318.IsUniversal
    (DerivationOpenRestriction318.coefficients j φ) (D j φ) := by
  intro M d
  refine ⟨desc j φ d,desc_fac j φ d,?_⟩
  intro k hk
  exact hom_ext j φ (hk.trans (desc_fac j φ d).symm)

/-- Intrinsic relative differentials commute with restriction along every actual
open immersion, by a proved universal property on all module sheaves. -/
@[expose] def iso :
    UniversalSheafDifferentials318.omega (DerivationOpenRestriction318.coefficients j φ) ≅
      (UniversalSheafDifferentials318.omega φ).restrict j :=
  IntrinsicUniversalComparison318.isoOfUniversal _ (D j φ) (isUniversal j φ)

theorem iso_D :
    (UniversalSheafDifferentials318.D (DerivationOpenRestriction318.coefficients j φ)).postcomp
      (iso j φ).hom.val = D j φ :=
  IntrinsicUniversalComparison318.isoOfUniversal_fac _ _ _
end IntrinsicOpenRestriction318
