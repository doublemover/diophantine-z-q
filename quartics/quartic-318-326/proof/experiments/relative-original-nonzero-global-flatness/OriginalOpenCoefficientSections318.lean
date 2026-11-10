module
public import OriginalCoefficientImageScalar318
public import OriginalOpenPullbackSections318
public import OriginalLineAffineModel318
public section
noncomputable section
namespace OriginalOpenCoefficientSections318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalCoefficientCohomology318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R B : CommRingCat.{0}) {X : Scheme.{0}} (p : X ⟶ Spec R)
  (j : Spec B ⟶ X) [IsOpenImmersion j] (g : R ⟶ B)
  (hj : j ≫ p = Spec.map g) (L : Line X)
local instance : Module R (OriginalLineAffineModel318.sections B (LineSheafPullback318.line j L)) :=
  Module.compHom _ g.hom
local instance : Module R Γ(L.object,j ''ᵁ ⊤) := sectionModule R p L _

/-- The unchanged whole affine-open section equivalence is linear for
BOTH independently defined structural coefficient actions. -/
@[expose] def equivalence :
    OriginalLineAffineModel318.sections B (LineSheafPullback318.line j L) ≃ₗ[R]
      Γ(L.object,j ''ᵁ ⊤) where
  __ := OriginalOpenPullbackSections318.sectionsEquiv j L.object
  map_smul' r x := by
    change OriginalOpenPullbackSections318.sectionsEquiv j L.object
      ((Scheme.ΓSpecIso B).inv (g r) •
        (x : Γ((Scheme.Modules.pullback j).obj L.object,⊤))) =
      scalar R p (j ''ᵁ ⊤) r • OriginalOpenPullbackSections318.sectionsEquiv j L.object x
    rw [OriginalOpenPullbackSectionScalar318.scalar,
      OriginalCoefficientImageScalar318.image_scalar R B p j g hj]
end OriginalOpenCoefficientSections318
