module
public import ContactProjectiveGlobalClassifyingMap318
public import ContactHilbertLocalClassifier318
public section
noncomputable section
namespace ContactHilbertLocalIdeal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactHilbertData318 ContactQuotientChart318
open scoped TensorProduct
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (n : ℕ) (D : FixedRank S c n)
local notation "Db" => ContactHilbertLocalClassifier318.bounded S c n D
local notation "U" => ContactHilbertLocalClassifier318.cover S c n D
@[expose] def coefficients : AffineCoefficientCover318.Data ℚ S where
  Index := U.I₀
  ring := ContactHilbertAvoidanceAffineCover318.ring S c n Db
  algebra := ContactHilbertAvoidanceAffineCover318.algebra S c n Db
  coefficient := ContactHilbertAvoidanceAffineCover318.coefficient S c n Db
  open_map i := by rw [ContactHilbertAvoidanceAffineCover318.coefficient_spec]; infer_instance
  covers x := by
    obtain ⟨i,y,hy⟩ := U.openCover.exists_eq x
    refine ⟨i,?_⟩
    rw [ContactHilbertAvoidanceAffineCover318.coefficient_spec]
    exact ⟨y,hy⟩
variable (a : U.I₀)
local notation "T" => ContactHilbertAvoidanceAffineCover318.ring S c n Db a
local notation "j" => ContactHilbertAvoidanceAffineCover318.chart S c n Db a
local notation "f" => ContactHilbertAffineWholeFamily318.affineInto S c n Db a
@[expose] def chart : Chart := ⟨ContactOriginalLinearOpenChart318.linearForm (j.val : ℚ),
  ContactOriginalLinearOpenChart318.linearForm_homogeneous (j.val : ℚ)⟩
local notation "A" => ring c (chart S c n D a)
local instance finite : IsFinite (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change IsFinite (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactHilbertAffineWholeFamily318.affine_projection]; infer_instance
local instance flat : Flat (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change Flat (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactHilbertAffineWholeFamily318.affine_projection]; infer_instance
local instance presentation : LocallyOfFinitePresentation (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change LocallyOfFinitePresentation (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactHilbertAffineWholeFamily318.affine_projection]; infer_instance
@[expose] def ideal : Ideal c (chart S c n D a) T n :=
  AffineFiniteProjectiveQuotient318.data ℚ A T f (Fin n) (ContactHilbertLocalClassifier318.rank S c n D a)
/-- Actual literal quotient presentation of the entire original local
family, with no finite assumption on a fixed source-chart restriction. -/
@[expose] def comparison : family c (chart S c n D a) T n (ideal S c n D a) ≅
    ContactHilbertAffineWholeFamily318.family S c n Db a :=
  (AffineClosedQuotientExtraction318.comparison (T ⊗[ℚ] A) f).symm
@[reassoc] lemma comparison_into : (comparison S c n D a).hom ≫ ContactHilbertAffineWholeFamily318.into S c n Db a=
    projectiveInto c (chart S c n D a) T n (ideal S c n D a) := by
  let u := ContactRelativeLinearOpenChart318.into T c (chart S c n D a).form (chart S c n D a).homogeneous
  calc
    _ = (comparison S c n D a).hom ≫ (f ≫ u) :=
      congrArg (fun k => (comparison S c n D a).hom ≫ k)
        (ContactHilbertAffineWholeFamily318.affine_into S c n Db a).symm
    _ = ((comparison S c n D a).hom ≫ f) ≫ u := (Category.assoc _ _ _).symm
    _ = quotientInto c (chart S c n D a) T n (ideal S c n D a) ≫ u :=
      congrArg (fun k => k ≫ u) (AffineClosedQuotientExtraction318.comparison_inv_into (T ⊗[ℚ] A) f)
    _ = _ := rfl
end ContactHilbertLocalIdeal318
