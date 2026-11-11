module
public import ContactProjectiveGlobalClassifyingMap318
public import ContactFixedDegreeLocalClassifier318
public section
noncomputable section
namespace ContactFixedDegreeLocalIdeal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveDegreeData318 ContactQuotientChart318
open scoped TensorProduct
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (n : ℕ) (D : FixedDegree S c n)
local notation "Db" => ContactFixedDegreeLocalClassifier318.bounded S c n D
local notation "U" => ContactFixedDegreeLocalClassifier318.cover S c n D
@[expose] def coefficients : AffineCoefficientCover318.Data ℚ S where
  Index := U.I₀
  ring := ContactBoundedAvoidanceAffineCover318.ring S c n Db
  algebra := ContactBoundedAvoidanceAffineCover318.algebra S c n Db
  coefficient := ContactBoundedAvoidanceAffineCover318.coefficient S c n Db
  open_map i := by rw [ContactBoundedAvoidanceAffineCover318.coefficient_spec]; infer_instance
  covers x := by
    obtain ⟨i,y,hy⟩ := U.openCover.exists_eq x
    refine ⟨i,?_⟩
    rw [ContactBoundedAvoidanceAffineCover318.coefficient_spec]
    exact ⟨y,hy⟩
variable (a : U.I₀)
local notation "T" => ContactBoundedAvoidanceAffineCover318.ring S c n Db a
local notation "j" => ContactBoundedAvoidanceAffineCover318.chart S c n Db a
local notation "f" => ContactAvoidanceAffineWholeFamily318.affineInto S c n Db a
@[expose] def chart : Chart := ⟨ContactOriginalLinearOpenChart318.linearForm (j.val : ℚ),
  ContactOriginalLinearOpenChart318.linearForm_homogeneous (j.val : ℚ)⟩
local notation "A" => ring c (chart S c n D a)
local instance finite : IsFinite (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change IsFinite (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactAvoidanceAffineWholeFamily318.affine_projection]; infer_instance
local instance flat : Flat (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change Flat (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactAvoidanceAffineWholeFamily318.affine_projection]; infer_instance
local instance presentation : LocallyOfFinitePresentation (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change LocallyOfFinitePresentation (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactAvoidanceAffineWholeFamily318.affine_projection]; infer_instance
@[expose] def ideal : Ideal c (chart S c n D a) T n :=
  AffineFiniteProjectiveQuotient318.data ℚ A T f (Fin n) (ContactFixedDegreeLocalClassifier318.rank S c n D a)
/-- Actual literal quotient presentation of the entire original local
family, with no finite assumption on a fixed source-chart restriction. -/
@[expose] def comparison : family c (chart S c n D a) T n (ideal S c n D a) ≅
    ContactAvoidanceAffineWholeFamily318.family S c n Db a :=
  (AffineClosedQuotientExtraction318.comparison (T ⊗[ℚ] A) f).symm
@[reassoc] lemma comparison_into : (comparison S c n D a).hom ≫ ContactAvoidanceAffineWholeFamily318.into S c n Db a=
    projectiveInto c (chart S c n D a) T n (ideal S c n D a) := by
  let u := ContactRelativeLinearOpenChart318.into T c (chart S c n D a).form (chart S c n D a).homogeneous
  calc
    _ = (comparison S c n D a).hom ≫ (f ≫ u) :=
      congrArg (fun k => (comparison S c n D a).hom ≫ k)
        (ContactAvoidanceAffineWholeFamily318.affine_into S c n Db a).symm
    _ = ((comparison S c n D a).hom ≫ f) ≫ u := (Category.assoc _ _ _).symm
    _ = quotientInto c (chart S c n D a) T n (ideal S c n D a) ≫ u :=
      congrArg (fun k => k ≫ u) (AffineClosedQuotientExtraction318.comparison_inv_into (T ⊗[ℚ] A) f)
    _ = _ := rfl
end ContactFixedDegreeLocalIdeal318
