module
public import TildePullbackMate318
public section
noncomputable section
namespace AffineComparisonMates318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- Equality transport of actual pullbacks is conjugate to the inverse
of actual equality transport of pushforwards. -/
lemma congr_inverse_mate {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackCongr h).inv =
        (Scheme.Modules.pushforwardCongr h).hom := by
  cases h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv,
    conjugateEquiv_id]
  ext M U
  simp

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)

/-- The actual sheaf composition comparison on spectra. -/
@[expose] def pullbackComp :
    Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map g) ≅
      Scheme.Modules.pullback (Spec.map (f ≫ g)) :=
  Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
    Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm

lemma pullbackComp_inverse_mate :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
      (pullbackComp f g).inv = (AffineGlobalSectionCoherence318.specComp f g).hom := by
  change conjugateEquiv _ _
    ((Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).inv ≫
      (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).inv) = _
  rw [← conjugateEquiv_comp _
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g ≫ Spec.map f)),
    Scheme.Modules.conjugateEquiv_pullbackComp_inv, congr_inverse_mate]
  rfl

lemma scalarComp_mate :
    conjugateEquiv
      ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
        (ModuleCat.extendRestrictScalarsAdj g.hom))
      (ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom)
      (ModuleCat.extendScalarsComp f.hom g.hom).hom =
        (ModuleCat.restrictScalarsComp f.hom g.hom).inv := by
  rw [CommRingCat.hom_comp]
  simp only [ModuleCat.extendScalarsComp, conjugateIsoEquiv_symm_apply_hom,
    Iso.symm_hom, Equiv.apply_symm_apply]
end AffineComparisonMates318
