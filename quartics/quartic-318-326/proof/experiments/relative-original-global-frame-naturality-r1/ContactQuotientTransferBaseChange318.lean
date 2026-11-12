module
public import ContactQuotientChartCoefficient318
public section
noncomputable section
namespace ContactQuotientTransferBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientChartTransfer318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (a b : Chart) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) (n : ℕ) (I : Ideal c a S n) (h : Supported c a b S n I)
local notation "J" => ContactQuotientChartCoefficient318.extended c a S T φ n I
local notation "ht" => ContactQuotientChartCoefficient318.supported c a S T φ n I b h
local notation "k" => ContactQuotientChartCoefficient318.map c a S T φ n I
local notation "f" => lift c a b S n I h
local notation "g" => lift c a b T n J ht
@[reassoc] lemma square : k ≫ f=g ≫ VaryingSourceCoefficientPullback318.sourceChange ℚ (ring c b) S T φ := by
  apply (cancel_mono (into c b S)).mp
  have hs := RelativeCoefficientChange318.into_square (CommRingCat.of ℚ) S T (ring c b) φ
    (ContactIntrinsicDifferentials318.structureMap c) (original c b)
    (ContactOriginalLinearOpenChart318.affine_over c b.form b.homogeneous)
  calc
    _ = k ≫ projectiveInto c a S n I := by rw [Category.assoc,lift_into]
    _ = projectiveInto c a T n J ≫ RelativeCoefficientChange318.familyMap
        (CommRingCat.of ℚ) S T φ (ContactIntrinsicDifferentials318.structureMap c) :=
      ContactQuotientChartCoefficient318.map_projective c a S T φ n I
    _ = (g ≫ into c b T) ≫ RelativeCoefficientChange318.familyMap
        (CommRingCat.of ℚ) S T φ (ContactIntrinsicDifferentials318.structureMap c) :=
      congrArg (fun u => u ≫ RelativeCoefficientChange318.familyMap
        (CommRingCat.of ℚ) S T φ (ContactIntrinsicDifferentials318.structureMap c))
          (lift_into c a b T n J ht).symm
    _ = g ≫ (into c b T ≫ RelativeCoefficientChange318.familyMap
        (CommRingCat.of ℚ) S T φ (ContactIntrinsicDifferentials318.structureMap c)) := Category.assoc _ _ _
    _ = g ≫ (VaryingSourceCoefficientPullback318.sourceChange ℚ (ring c b) S T φ ≫ into c b S) :=
      congrArg (fun u => g ≫ u) hs.symm
    _ = _ := (Category.assoc _ _ _).symm
/-- The reclassified closed families form the ACTUAL source tensor
Cartesian square, not merely a square on point labels. -/
lemma cartesian : IsPullback k g f (VaryingSourceCoefficientPullback318.sourceChange ℚ (ring c b) S T φ) := by
  apply IsPullback.of_bot
    (v₂₁ := VaryingSourceCoefficientPullback318.projection ℚ (ring c b) T)
    (v₂₂ := VaryingSourceCoefficientPullback318.projection ℚ (ring c b) S)
  · simpa only [lift_projection] using ContactQuotientChartCoefficient318.cartesian c a S T φ n I
  · exact square c a b S T φ n I h
  · exact VaryingSourceCoefficientPullback318.cartesian ℚ (ring c b) S T φ
/-- The complete extracted quotient ideal commutes with EVERY
coefficient ring map. No flatness is imposed on that ring map. -/
lemma natural : transfer c a b T n J ht=
    VaryingProjectiveQuotientNaturality318.mapIdeal ℚ (ring c b) (Fin n) S T φ (transfer c a b S n I h) := by
  apply Subtype.ext
  exact AffineClosedIdealBaseChange318.ideal_map (S ⊗[ℚ] ring c b) (T ⊗[ℚ] ring c b)
    (VaryingNormalizedIdealBaseChange318.sourceMap ℚ (ring c b) S T φ).toRingHom f g k
    (cartesian c a b S T φ n I h)
end ContactQuotientTransferBaseChange318
