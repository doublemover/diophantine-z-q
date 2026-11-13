module
public import ProjectiveKernelScalarNaturalRebuild318
public import ProjectiveKernelSliceOriginalRebuild318
public import ProjectiveKernelOverlapSchemes318
public section
noncomputable section
namespace ProjectiveKernelOverlapOriginalRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "K" => ProjectiveKernelParameter318.algebra R P Q d
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d
local notation "D" => ProjectiveKernelOverlapAlgebras318.ring R P Q d
local notation "q" => ProjectiveKernelOverlapAlgebras318.quotient R P Q d
variable (i j : Fin F.size)
/-- The literal left quotient map, retaining its actual R-algebra action. -/
def leftAlgebra : C i →ₐ[R] D i j where
  __ := (ProjectiveKernelOverlapAlgebras318.leftRing R P Q d i j).hom
  commutes' r := rfl

def leftPoint : K →ₐ[R] D i j :=
  (leftAlgebra R P Q d i j).comp (ProjectiveKernelSliceOriginalRebuild318.intoAlgebra R P Q d i)
def rightPoint : K →ₐ[R] D i j :=
  (ProjectiveKernelOverlapTransitions318.transition R P Q d i j).comp (leftPoint R P Q d j i)
def ratio : (D i j)ˣ := Units.map (q i j).toMonoidHom
  (ProjectiveParameterSliceLocalization318.unit R P i j)⁻¹
lemma left_ambient : (leftPoint R P Q d i j).comp (ProjectiveKernelParameter318.quotient R P Q d) =
    (q i j).comp (ProjectiveParameterSliceLocalization318.point R P i j) := by
  apply AlgHom.ext
  intro a
  rfl
/-- The two ORIGINAL kernel points on the FULL overlap differ by the
actual inverse transition coordinate, not by an unspecified scalar. -/
lemma right_scaled : rightPoint R P Q d i j =
    ProjectiveKernelScalarActionRebuild318.pointScale R P Q d (D i j)
      (ratio R P Q d i j : D i j) (leftPoint R P Q d i j) := by
  apply Ideal.Quotient.algHom_ext
  rw [ProjectiveKernelScalarActionRebuild318.ambient]
  change ((ProjectiveKernelOverlapTransitions318.transition R P Q d i j).comp
    (leftPoint R P Q d j i)).comp (ProjectiveKernelParameter318.quotient R P Q d) = _
  rw [AlgHom.comp_assoc,left_ambient,←AlgHom.comp_assoc,
    ProjectiveKernelOverlapTransitions318.transition_quotient,left_ambient]
  apply AlgHom.ext
  intro a
  change q i j (ProjectiveParameterSliceLocalization318.transition R P i j
    (ProjectiveParameterSliceLocalization318.point R P j i a)) = _
  rw [ProjectiveParameterSliceLocalization318.transition_point]
  exact DFunLike.congr_fun
    (ProjectiveParameterUnitAction318.pointScale_natural R P _ (q i j)
      (((ProjectiveParameterSliceLocalization318.unit R P i j)⁻¹ : _) : _)
      (ProjectiveParameterSliceLocalization318.point R P i j)) a
@[reassoc] lemma left_original : ProjectiveKernelOverlapAlgebras318.left R P Q d i j ≫
    ProjectiveKernelSliceOriginalRebuild318.into R P Q d i =
      Spec.map (CommRingCat.ofHom (leftPoint R P Q d i j).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [←Spec.map_comp] <;> rfl
@[reassoc] lemma right_original : ProjectiveKernelOverlapSchemes318.right R P Q d i j ≫
    ProjectiveKernelSliceOriginalRebuild318.into R P Q d j =
      Spec.map (CommRingCat.ofHom (rightPoint R P Q d i j).toRingHom) := by
  change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = _
  rw [←Spec.map_comp,←Spec.map_comp] <;> rfl
end ProjectiveKernelOverlapOriginalRebuild318
