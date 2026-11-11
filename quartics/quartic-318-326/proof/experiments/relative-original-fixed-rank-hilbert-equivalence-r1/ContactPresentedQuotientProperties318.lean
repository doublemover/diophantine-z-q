module
public import ContactHilbertPresentation318
public section
noncomputable section
namespace ContactPresentedQuotientProperties318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  {Z : Scheme.{0}} (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c) [IsClosedImmersion q]
  (D : ContactProjectiveLocalPresentation318.Data c n S q)
local notation "π" => q ≫ ContactRelativeLinearOpenChart318.projection S c
local notation "C" => D.coefficients
local notation "U" => AffineCoefficientCover318.cover ℚ S C
/-- The local full finite-projective presentations imply the standard
WHOLE-family finite-flat finite-presentation properties. -/
lemma finite : IsFinite π := by
  apply IsZariskiLocalAtTarget.of_openCover U
  intro i
  rw [← (ContactProjectiveInputRecovery318.left_cartesian c n S q D i).isoPullback_inv_snd]
  infer_instance
lemma flat : Flat π := by
  apply IsZariskiLocalAtTarget.of_openCover U
  intro i
  rw [← (ContactProjectiveInputRecovery318.left_cartesian c n S q D i).isoPullback_inv_snd]
  infer_instance
lemma presentation : LocallyOfFinitePresentation π := by
  apply IsZariskiLocalAtTarget.of_openCover U
  intro i
  rw [← (ContactProjectiveInputRecovery318.left_cartesian c n S q D i).isoPullback_inv_snd]
  infer_instance
/-- Rank n holds at EVERY coefficient prime, by the actual Cartesian
rank formula and the entire coefficient cover, not a chosen global frame. -/
lemma rank (x : PrimeSpectrum S) : π.finrank x=n := by
  letI := finite c n S q D
  obtain ⟨i,y,hy⟩ := U.exists_eq x
  have h := ContactQuotientChart318.rank c (D.chart i) (C.ring i) n (D.ideal i) y
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _
    (ContactProjectiveInputRecovery318.left_cartesian c n S q D i)] at h
  simpa only [hy,Fintype.card_fin] using h
end ContactPresentedQuotientProperties318
