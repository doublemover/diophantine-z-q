module
public import ContactQuotientTransferBaseChange318
public section
noncomputable section
namespace ContactQuotientOverlapNaturality318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientOverlapEquiv318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) (n : ℕ)
@[expose] def map (I : Overlap c a b S n) : Overlap c a b T n :=
  ⟨ContactQuotientChartCoefficient318.extended c a S T φ n I.val,
    ContactQuotientChartCoefficient318.supported c a S T φ n I.val b I.property⟩
/-- The genuine two-sided inter-source-chart equivalence is natural
under arbitrary coefficients, retaining the literal full ideals. -/
lemma natural (I : Overlap c a b S n) : equivalence c a b T n (map c a b S T φ n I)=
    map c b a S T φ n (equivalence c a b S n I) := by
  apply Subtype.ext
  exact ContactQuotientTransferBaseChange318.natural c a b S T φ n I.val I.property
end ContactQuotientOverlapNaturality318
