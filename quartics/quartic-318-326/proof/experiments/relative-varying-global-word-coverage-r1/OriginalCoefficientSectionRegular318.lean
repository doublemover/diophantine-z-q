module
public import OriginalCoefficientSections318
public import RankOneEvaluationFiber318
public section
noncomputable section
namespace OriginalCoefficientSectionRegular318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open scoped TensorProduct
universe u
variable (k R S B : CommRingCat.{u}) [Algebra k R] [Algebra k S] [Algebra k B]
  (f : R →ₐ[k] S)
local instance : Algebra R S := f.toAlgebra
variable {X : Scheme.{u}} (p : X ⟶ Spec k) (j : Spec B ⟶ X)
  (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k B)))
  (L : Line (RelativeOriginalAffineChart318.family k R p))
local notation "A" => (R ⊗[k] B)
local notation "C" => (S ⊗[k] B)
local notation "P" => OriginalCoefficientSections318.oldSections k R B p j hj L
local notation "Q" => OriginalCoefficientSections318.newSections k R S B f p j hj L
local instance : Module R P := Module.compHom P (algebraMap R A)
local instance : IsScalarTower R A P := IsScalarTower.of_compHom ..
local instance : Module S Q := Module.compHom Q (algebraMap S C)
local instance : IsScalarTower S C Q := IsScalarTower.of_compHom ..
local notation "E" => OriginalCoefficientSections318.equivalence k R S B f p j hj L
local notation "e" => OriginalCoefficientTensor318.ringEquivalence k R S B f
local notation "res" => OriginalCoefficientChartLine318.originalRestriction
  (RelativeCoefficientChange318.familyMap k R S f p)
  (RelativeCoefficientChange318.ringMap k R S B f)
  (RelativeOriginalAffineChart318.into k R B p j hj)
  (RelativeOriginalAffineChart318.into k S B p j hj)
  (RelativeCoefficientChange318.into_square k R S B f p j hj) L

/-- Exact square for multiplication by the SAME original section under
coefficient-only base change. Both original ring and line comparison
maps occur, and the actual geometric pullback unit determines the section. -/
lemma square (s : P) (z : S ⊗[R] A) :
    E ((RankOneEvaluationFiber318.section R A P s).baseChange S z) = e z • res s := by
  induction z using TensorProduct.inductionOn with
  | tmul t a =>
    have ht : t ⊗ₜ[R] a=t • ((1 : S) ⊗ₜ[R] a) := by
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.baseChange_tmul]
    change E (t ⊗ₜ[R] (a • s)) = _
    rw [OriginalCoefficientSections318.pure_tensor,
      OriginalCoefficientChartLine318.scalar]
    rw [ht, e.map_smul, OriginalCoefficientTensor318.ringEquivalence_right]
    exact (smul_assoc t (RelativeCoefficientChange318.ringMap k R S B f a) (res s)).symm
  | add z w hz hw =>
    simp only [map_add, hz, hw, add_smul]

/-- Geometric regularity of the literal new original-chart section
produces injectivity of the original coefficient-section map after
base change. No new coordinate, line model, or normalization is chosen. -/
lemma injective (s : P)
    (hs : Function.Injective (SectionZeroRegularCoordinate318.sectionMap C Q (res s))) :
    Function.Injective ((RankOneEvaluationFiber318.section R A P s).baseChange S) := by
  intro z w h
  apply e.injective
  apply hs
  change e z • res s=e w • res s
  rw [← square k R S B f p j hj L s z, ← square k R S B f p j hj L s w, h]
end OriginalCoefficientSectionRegular318
