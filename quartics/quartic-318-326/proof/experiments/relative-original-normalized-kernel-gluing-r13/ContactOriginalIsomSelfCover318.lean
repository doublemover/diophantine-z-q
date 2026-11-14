module
public import ContactOriginalLaurentShear318
public import FppfSingleCover318
public section
noncomputable section
namespace ContactOriginalIsomSelfCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L K
local notation "g" => LaurentWholeUnitRepresentation318.projection R
abbrev relation := pullback q q
abbrev second : relation R c L K ⟶ ContactGeometricIsomRelationWitness318.parameter R c L K := pullback.snd q q
/-- Smooth affine relation projection produced by the literal Laurent
shear. No smoothness or surjectivity of Isom -> coefficient base is assumed. -/
instance smooth : Smooth (second R c L K) := by
  haveI : Smooth g := LaurentProjectionSmooth318.smooth R
  rw [←ContactOriginalLaurentShear318.unshear_snd R c L K]
  infer_instance
instance affine : IsAffineHom (second R c L K) := by
  rw [←ContactOriginalLaurentShear318.unshear_snd R c L K]
  infer_instance
instance flat : Flat (second R c L K) := inferInstance
instance presentation : LocallyOfFinitePresentation (second R c L K) := inferInstance
@[expose] def diagonal : ContactGeometricIsomRelationWitness318.parameter R c L K ⟶ relation R c L K :=
  pullback.lift (𝟙 _) (𝟙 _) rfl
@[reassoc] lemma diagonal_second : diagonal R c L K ≫ second R c L K=𝟙 _ := pullback.lift_snd ..
instance surjective : Surjective (second R c L K) := by
  constructor
  intro x
  refine ⟨diagonal R c L K x,?_⟩
  have h := congrArg (fun f => f x) (diagonal_second R c L K)
  change second R c L K (diagonal R c L K x)=x at h
  exact h
/-- A genuine fppf cover of the original Isom space by its exact relation
space, including empty Isom spaces. This is NOT a cover of the entire base. -/
lemma covering : Sieve.ofArrows
    (fun _ : PUnit => Over.mk (second R c L K ≫ q))
    (fun _ => Over.homMk (second R c L K) (rfl : second R c L K ≫ q=second R c L K ≫ q)) ∈
      RelativeFppfLineSheaf318.topology (Spec R) (Over.mk q) :=
  FppfSingleCover318.covering q (second R c L K ≫ q) (second R c L K) rfl

end ContactOriginalIsomSelfCover318
