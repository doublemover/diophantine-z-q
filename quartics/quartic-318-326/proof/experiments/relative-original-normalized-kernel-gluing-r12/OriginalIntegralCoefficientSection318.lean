module
public import OriginalCoefficientSectionRegular318
public import IntegralAffineSectionRegular318
public import OriginalCoefficientGlobalUnit318
public section
noncomputable section
namespace OriginalIntegralCoefficientSection318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open OriginalSectionPullbackComposition318
open scoped TensorProduct
universe u
variable (k R S B : CommRingCat.{u}) [Algebra k R] [Algebra k S] [Algebra k B]
  (f : R →ₐ[k] S)
local instance : Algebra R S := f.toAlgebra
variable {X : Scheme.{u}} (p : X ⟶ Spec k) (j : Spec B ⟶ X)
  [IsOpenImmersion j]
  (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k B)))
  (L : Line (RelativeOriginalAffineChart318.family k R p))
local notation "A" => (R ⊗[k] B)
local notation "P" => OriginalCoefficientSections318.oldSections k R B p j hj L
local instance : Module R P := Module.compHom P (algebraMap R A)
local instance : IsScalarTower R A P := IsScalarTower.of_compHom ..
local notation "q" => RelativeCoefficientChange318.familyMap k R S f p
local notation "jR" => RelativeOriginalAffineChart318.into k R B p j hj
local notation "jS" => RelativeOriginalAffineChart318.into k S B p j hj
variable [IsIntegral (RelativeOriginalAffineChart318.family k S p)]

/-- Genuine geometric nonvanishing on the integral coefficient fiber
produces the exact coefficient-section tensor injectivity required by
flatness. The original whole chart may be empty; it is not assumed framed. -/
lemma injective (s : Γ(L.object,⊤)) (hs : pull q L.object s≠0) :
    Function.Injective ((RankOneEvaluationFiber318.section R A P
      (pull jR L.object s)).baseChange S) := by
  apply OriginalCoefficientSectionRegular318.injective k R S B f p j hj L
  rw [OriginalCoefficientGlobalUnit318.square q
    (RelativeCoefficientChange318.ringMap k R S B f) jR jS
    (RelativeCoefficientChange318.into_square k R S B f p j hj) L s]
  exact IntegralAffineSectionRegular318.open_pull (CommRingCat.of (S ⊗[k] B))
    jS (LineSheafPullback318.line q L) (pull q L.object s) hs
end OriginalIntegralCoefficientSection318
