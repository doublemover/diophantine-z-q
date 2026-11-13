module
public import ContactNowhereZeroResidueSourceRebuild318
public import SchemeResidueOpenLiftRebuild318
public section
noncomputable section
namespace ContactNowhereZeroSourceOpenRebuild318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "N" => ContactArbitraryNowhereZeroOpen318.scheme R c L
local notation "j" => ContactArbitraryNowhereZeroOpen318.into R c L
local notation "S" => ContactOriginalGlobalKernelNormalizationRebuild318.source R c L
local notation "q" => ContactOriginalGlobalKernelNormalizationRebuild318.original R c L
/-- The WHOLE original nowhere-zero open factors through the SAME full
kernel nonzero source. No H0 projectivity or field-only coverage is assumed. -/
def inclusion : N ⟶ S :=
  SchemeResidueOpenLiftRebuild318.lift q j (fun y =>
    ⟨(ContactNowhereZeroResidueSourceRebuild318.data R c L y).val,
      (ContactNowhereZeroResidueSourceRebuild318.data R c L y).property⟩)
@[reassoc] lemma original : inclusion R c L ≫ q = j :=
  SchemeResidueOpenLiftRebuild318.lift_fac _ _ _
instance inclusion_open : IsOpenImmersion (inclusion R c L) := by
  haveI : IsOpenImmersion (inclusion R c L ≫ q) := by rw [original]; infer_instance
  exact IsOpenImmersion.of_comp (inclusion R c L) q
lemma unique (a : N ⟶ S) (ha : a ≫ q = j) : a = inclusion R c L :=
  (cancel_mono q).mp (ha.trans (original R c L).symm)
/-- The constructed field witness and the whole open lift agree exactly. -/
@[reassoc] lemma residue (y : N) :
    N.fromSpecResidueField y ≫ inclusion R c L =
      (ContactNowhereZeroResidueSourceRebuild318.data R c L y).val := by
  apply (cancel_mono q).mp
  rw [Category.assoc,original]
  exact (ContactNowhereZeroResidueSourceRebuild318.data R c L y).property.symm
end ContactNowhereZeroSourceOpenRebuild318
