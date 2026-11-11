module
public import OpenPointScalarPullback318
public import OriginalOpenCoefficientSpecialization318
public import ReducedSchemeGlobalFunctionSeparation318
public section
noncomputable section
namespace ComplexOpenPointEvaluation318
open AlgebraicGeometry CategoryTheory
variable {X Y : Scheme}
@[expose] def evaluation (U : X.Opens) (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme) : Γ(X,U) →+* ℂ :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp p.appTop.hom).comp
    (LineFrameTopScalar318.ringTop U).inv.hom

lemma restriction (U V : X.Opens) (h : V≤U)
    (p : Spec (CommRingCat.of ℂ) ⟶ V.toScheme) (r : Γ(X,U)) :
    evaluation V p (X.presheaf.map (homOfLE h).op r)=
      evaluation U (p≫X.homOfLE h) r := by
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.appTop
    ((LineFrameTopScalar318.ringTop V).inv (X.presheaf.map (homOfLE h).op r)))=_
  have hr : (LineFrameTopScalar318.ringTop V).inv (X.presheaf.map (homOfLE h).op r)=
      (X.homOfLE h).appTop ((LineFrameTopScalar318.ringTop U).inv r) := by
    have hs := OriginalOpenCoefficientSpecialization318.coefficient_pullback U V h
      ((LineFrameTopScalar318.ringTop U).inv r)
    simpa only [GlobalSectionFrameCoordinates318.coefficient,Iso.inv_hom_id_apply] using hs
  rw [hr]
  rfl

lemma pullback (f : Y ⟶ X) (U : X.Opens)
    (p : Spec (CommRingCat.of ℂ) ⟶ (f ⁻¹ᵁ U).toScheme)
    (q : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (h : p≫(f ⁻¹ᵁ U).ι≫f=q≫U.ι) (r : Γ(X,U)) :
    evaluation (f ⁻¹ᵁ U) p (f.app U r)=evaluation U q r :=
  (OpenPointScalarPullback318.evaluation_pullback f U r p q h).symm

/-- Full regular-function separation on arbitrary original scheme
opens; reducedness and the actual finite-type complex base are explicit. -/
lemma ext (π : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType π] [IsReduced X]
    (U : X.Opens) (r s : Γ(X,U))
    (h : ∀ (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme),p≫U.ι≫π=𝟙 _ →
      evaluation U p r=evaluation U p s) : r=s := by
  apply (LineFrameTopScalar318.ringTop U).inv.injective
  apply ReducedSchemeGlobalFunctionSeparation318.ext (U.ι≫π)
  intro p hp
  apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.injective
  exact h p hp

lemma isUnit (π : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType π]
    (U : X.Opens) (r : Γ(X,U))
    (h : ∀ (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme),p≫U.ι≫π=𝟙 _ →
      evaluation U p r≠0) : IsUnit r := by
  have hu : IsUnit ((LineFrameTopScalar318.ringTop U).inv r) := by
    apply ReducedSchemeGlobalFunctionSeparation318.isUnit (U.ι≫π)
    intro p hp
    have hv := isUnit_iff_ne_zero.mpr (h p hp)
    change IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (p.appTop ((LineFrameTopScalar318.ringTop U).inv r))) at hv
    simpa only [←ConcreteCategory.comp_apply,Iso.hom_inv_id,ConcreteCategory.id_apply] using
      hv.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
  simpa only [Iso.inv_hom_id_apply] using hu.map (LineFrameTopScalar318.ringTop U).hom
end ComplexOpenPointEvaluation318
