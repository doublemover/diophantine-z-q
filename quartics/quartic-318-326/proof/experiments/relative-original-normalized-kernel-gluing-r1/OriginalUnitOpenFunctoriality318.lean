module
public import OriginalLineDerivedPullback318
public import OriginalSectionPullbackComposition318
public section
noncomputable section
namespace OriginalUnitOpenFunctoriality318
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Original pullback units compose on EVERY ambient open, retaining
the genuine module-sheaf associator, not just on global affine sections. -/
lemma composition (M : Z.Modules) (U : Z.Opens) (s : Γ(M,U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M)).app (g ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U s)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hs := congrArg (fun q => q.app U s) h
  change _ = ((Scheme.Modules.pullbackComp f g).inv.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
    (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s) at hs
  rw [hs]
  exact congrArg (fun q => q.app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
    (((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U s))
      ((Scheme.Modules.pullbackComp f g).inv_hom_id_app M)

lemma identity (M : X.Modules) (U : X.Opens) (s : Γ(M,U)) :
    ((Scheme.Modules.pullbackId X).hom.app M).app U
      (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).unit.app M).app U s) = s := by
  have h := unit_conjugateEquiv Adjunction.id
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)) (Scheme.Modules.pullbackId X).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (congrArg (fun q => q.app U s) h).symm
end OriginalUnitOpenFunctoriality318
