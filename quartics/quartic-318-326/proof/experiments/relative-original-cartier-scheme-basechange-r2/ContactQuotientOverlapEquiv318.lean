module
public import ContactQuotientTransferCocycle318
public section
noncomputable section
namespace ContactQuotientOverlapEquiv318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientChartTransfer318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (S : CommRingCat.{0}) [Algebra ℚ S] (n : ℕ)
/-- Overlap inputs are defined intrinsically by whole original support,
not as the image of the transfer function. -/
abbrev Overlap := {I : Ideal c a S n // Supported c a b S n I}
/-- Genuine two-sided equivalence between the two source-chart quotient
functors on their actual mutual-support overlap. -/
@[expose] def equivalence : Overlap c a b S n ≃ Overlap c b a S n where
  toFun I := ⟨transfer c a b S n I.val I.property,
    ContactQuotientTransferSupport318.reverse c a b S n I.val I.property⟩
  invFun J := ⟨transfer c b a S n J.val J.property,
    ContactQuotientTransferSupport318.reverse c b a S n J.val J.property⟩
  left_inv I := Subtype.ext (ContactQuotientTransferRecovery318.inverse c a b S n I.val I.property)
  right_inv J := Subtype.ext (ContactQuotientTransferRecovery318.inverse c b a S n J.val J.property)
end ContactQuotientOverlapEquiv318
