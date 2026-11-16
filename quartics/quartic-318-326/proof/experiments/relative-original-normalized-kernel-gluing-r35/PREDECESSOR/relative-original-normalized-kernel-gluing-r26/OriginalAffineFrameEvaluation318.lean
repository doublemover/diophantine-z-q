module
public import OriginalAffineGeneratorPullback318
public import UniversalCoordinateGeneration318
public section
noncomputable section
namespace OriginalAffineFrameEvaluation318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R A B : CommRingCat.{u}) [Algebra R A] (f : A ⟶ B)
  (L : Line (Spec A)) (N : Line (Spec B))
  (e : (Scheme.Modules.pullback (Spec.map f)).obj L.object ≅ N.object)
  (v : OriginalLineAffineModel318.sections B N ≃ₗ[B] B)
local instance : Algebra R B := (f.hom.comp (algebraMap R A)).toAlgebra
local instance : Module R (OriginalLineAffineModel318.sections A L) :=
  Module.compHom _ (algebraMap R A)
local instance : IsScalarTower R A (OriginalLineAffineModel318.sections A L) := IsScalarTower.of_compHom ..
variable (P : Type u) [AddCommGroup P] [Module R P]
  (ρ : P →ₗ[R] OriginalLineAffineModel318.sections A L)

/-- Actual global restriction, original affine geometric pullback unit,
and specified original local rank-one frame. No arbitrary functional is
substituted for this geometric section-coordinate map. -/
@[expose] def evaluation : P →ₗ[R] B where
  toFun s := v (OriginalAffineLinePathSections318.restriction f L N e (ρ s))
  map_add' s t := by rw [map_add,OriginalAffineLinePathSections318.restriction_add,map_add]
  map_smul' r s := by
    rw [map_smul,← IsScalarTower.algebraMap_smul A r (ρ s),
      OriginalAffineLinePathSections318.restriction_smul,map_smul]
    rfl

/-- Original chart generation is consumed AFTER the actual pullback and
actual local frame; hence the value-one producer applies at its use site. -/
lemma span (h : Submodule.span A (Set.range ρ)=⊤) :
    Submodule.span B (Set.range (evaluation R A B f L N e v P ρ))=⊤ :=
  OriginalAffineGeneratorPullback318.frame_span f L N e ρ h v

variable [Module.Finite R P] [Module.Projective R P]

/-- Actual local framed evaluation gives a regular coefficient of the
SAME universal section tensor. Neither flatness of the base map nor a
primitive section is assumed: the latter is produced from chart generation. -/
theorem regular (h : Submodule.span A (Set.range ρ)=⊤)
    (a : B ⊗[R] ProjectiveSectionParameter318.algebra R P)
    (ha : a * UniversalScalarCoordinate318.coefficient R P B
      (evaluation R A B f L N e v P ρ)=0) : a=0 :=
  UniversalCoordinateGeneration318.regular R P B (evaluation R A B f L N e v P ρ)
    (span R A B f L N e v P ρ h) a ha
end OriginalAffineFrameEvaluation318
