module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import ActualOpenImmersionLineFrame318
public section
noncomputable section
namespace AffineCokernelSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : CommRingCat.{u}} {M N : (Spec R).Modules} (d : M ⟶ N)

/-- The ordinary quotient of the ACTUAL affine sections map. No chosen
free coordinates or replacement coefficient map enters this definition. -/
abbrev sectionQuotient :=
  (moduleSpecΓFunctor.obj N) ⧸ LinearMap.range (moduleSpecΓFunctor.map d).hom

/-- For affine sheaves whose actual tilde-section counits are isomorphisms,
the real sheaf cokernel is tilde of the real module quotient. This does NOT
assert that sections preserve arbitrary sheaf cokernels. -/
@[expose] def iso [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] :
    cokernel d ≅ tilde (R := R) (ModuleCat.of R (sectionQuotient d)) :=
  (cokernel.mapIso ((tilde.functor R).map (moduleSpecΓFunctor.map d)) d
    (asIso M.fromTildeΓ) (asIso N.fromTildeΓ)
    (Scheme.Modules.fromTildeΓNatTrans.naturality d)).symm ≪≫
  (PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map d)).symm ≪≫
  (tilde.functor R).mapIso (ModuleCat.cokernelIsoRangeQuotient (moduleSpecΓFunctor.map d))

/-- A supplied genuine free rank-one SHEAF frame proves the actual
counit is an isomorphism, rather than assuming affine section exactness. -/
theorem counit_isIso_of_frame (A : (Spec R).Modules)
    (e : SheafOfModules.unit (Spec R).ringCatSheaf ≅ A) : IsIso A.fromTildeΓ :=
  isIso_fromTildeΓ_iff.mpr ⟨ModuleCat.of R R,⟨tildeSelf ≪≫ e⟩⟩

/-- Recover the chart frame from a frame on its genuine ambient open
image. All restriction functors use the original open-immersion square. -/
@[expose] def chartFrame {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (A : Y.Modules)
    (e : SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf ≅ A.restrict j.opensRange.ι) :
    SheafOfModules.unit X.ringCatSheaf ≅ A.restrict j :=
  (Scheme.Modules.restrictUnitIso (ActualOpenImmersionLineFrame318.imageIso j).hom).symm ≪≫
  (Scheme.Modules.restrictFunctor (ActualOpenImmersionLineFrame318.imageIso j).hom).mapIso e ≪≫
  ((Scheme.Modules.restrictFunctorComp (ActualOpenImmersionLineFrame318.imageIso j).hom
    j.opensRange.ι).symm.app A) ≪≫
  ((Scheme.Modules.restrictFunctorCongr (ActualOpenImmersionLineFrame318.image_square j)).app A)

/-- Restriction is a left adjoint. Thus the restricted WHOLE cokernel is
the chart cokernel before passing through the actual affine section comparison. -/
@[expose] def restrictionIso {X : Scheme.{u}} (j : Spec R ⟶ X) [IsOpenImmersion j]
    {A B : X.Modules} (a : A ⟶ B)
    [IsIso (A.restrict j).fromTildeΓ] [IsIso (B.restrict j).fromTildeΓ] :
    (cokernel a).restrict j ≅ tilde (R := R)
      (ModuleCat.of R (sectionQuotient ((Scheme.Modules.restrictFunctor j).map a))) :=
  PreservesCokernel.iso (Scheme.Modules.restrictFunctor j) a ≪≫
    iso ((Scheme.Modules.restrictFunctor j).map a)
end AffineCokernelSections318
