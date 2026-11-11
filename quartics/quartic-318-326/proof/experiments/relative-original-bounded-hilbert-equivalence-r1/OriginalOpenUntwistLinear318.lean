module
public import OriginalOpenPullbackSectionScalar318
public import OriginalLineAffineModel318
public section
noncomputable section
namespace OriginalOpenUntwistLinear318
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (B : CommRingCat.{u}) {X : Scheme.{u}} (j : Spec B ⟶ X) [IsOpenImmersion j]
  (M N : X.Modules) (e : Γ(M,j ''ᵁ ⊤) ≃ₗ[Γ(X,j ''ᵁ ⊤)] Γ(N,j ''ᵁ ⊤))

/-- A specified original ambient frame comparison induces an equivalence
of the ACTUAL affine pulled section modules over the full chart ring.
Both scalar changes are the same original open-immersion ring map. -/
@[expose] def equivalence :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback j).obj M) ≃ₗ[B]
      moduleSpecΓFunctor.obj ((Scheme.Modules.pullback j).obj N) where
  __ := (OriginalOpenPullbackSections318.sectionsEquiv j M).trans
    (e.toAddEquiv.trans (OriginalOpenPullbackSections318.sectionsEquiv j N).symm)
  map_smul' b x := by
    apply (OriginalOpenPullbackSections318.sectionsEquiv j N).injective
    change e (OriginalOpenPullbackSections318.sectionsEquiv j M
      ((Scheme.ΓSpecIso B).inv b • x)) =
        OriginalOpenPullbackSections318.sectionsEquiv j N
          ((Scheme.ΓSpecIso B).inv b •
            (OriginalOpenPullbackSections318.sectionsEquiv j N).symm
              (e (OriginalOpenPullbackSections318.sectionsEquiv j M x)))
    rw [OriginalOpenPullbackSectionScalar318.scalar,
      OriginalOpenPullbackSectionScalar318.scalar,AddEquiv.apply_symm_apply,map_smul]
end OriginalOpenUntwistLinear318
