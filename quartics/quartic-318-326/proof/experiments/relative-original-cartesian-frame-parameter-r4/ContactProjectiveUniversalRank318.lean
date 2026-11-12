module
public import ContactSchemeHilbertRule318
public section
noncomputable section
namespace ContactProjectiveUniversalRank318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ)
local notation "b" => ContactProjectiveParameterStructure318.structureMap c n
local notation "π" => ContactProjectiveUniversalProjection318.projection c n
/-- True constant fiber rank on EVERY point of the whole projective
quotient parameter, proved through its entire affine coefficient cover. -/
lemma rank (z : ContactProjectiveQuotientParameter318.scheme c n) : π.finrank z=n := by
  let U := RelativeAffineTestCover318.cover ℚ b
  obtain ⟨i,y,hy⟩ := U.openCover.exists_eq z
  let S := RelativeAffineTestCover318.ring ℚ b i
  let x : ContactProjectiveParameterPoint318.Point c n S := RelativeAffineTestCover318.point ℚ b i
  have h := ContactPresentedQuotientProperties318.rank c n S (ContactProjectivePointFamily318.into c n S x)
    (ContactProjectivePointPresentation318.data c n S x) y
  rw [ContactProjectivePointFamily318.into_base] at h
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (IsPullback.of_hasPullback π x.val)] at h
  simpa only [hy] using h
end ContactProjectiveUniversalRank318
