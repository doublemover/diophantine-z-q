module
public import RelativeOriginalAffineChart318
public section
noncomputable section
namespace RelativeAffineChartCartesian318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R S A : CommRingCat.{u}) [Algebra R S] [Algebra R A]
  {X : Scheme.{u}} (a : X ⟶ Spec R) (j : Spec A ⟶ X) [IsOpenImmersion j]
  (hj : j ≫ a=Spec.map (CommRingCat.ofHom (algebraMap R A)))
local notation "f" => RelativeOriginalAffineChart318.baseMap R S
local notation "J" => RelativeOriginalAffineChart318.into R S A a j hj
local notation "g" => Spec.map (CommRingCat.ofHom
  (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom)
/-- The actual tensor chart is Cartesian over the original chart, with
both literal projections retained. -/
lemma cartesian : IsPullback g J j (pullback.fst a f) := by
  apply IsPullback.of_iso_pullback (i := (RelativeOriginalAffineChart318.chartIso R S A a j hj).symm)
  · constructor
    exact (RelativeOriginalAffineChart318.over_original R S A a j hj).symm
  · apply (cancel_mono j).mp
    rw [Category.assoc,pullback.condition,← Category.assoc]
    exact RelativeOriginalAffineChart318.over_original R S A a j hj
  · rfl
end RelativeAffineChartCartesian318
