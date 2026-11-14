module
public import ContactQuotientTransferIsoInvariant318
public section
noncomputable section
namespace ContactQuotientTransferCocycle318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientChartTransfer318
variable (c : Fin 4 → ℚˣ) (a b d : Chart) (S : CommRingCat.{0}) [Algebra ℚ S]
  (n : ℕ) (I : Ideal c a S n)
  (hb : Supported c a b S n I) (hd : Supported c a d S n I)
/-- Exact full-ideal cocycle on EVERY triple-supported original family.
No reduced or geometric-point-only comparison is used. -/
lemma cocycle : transfer c b d S n (transfer c a b S n I hb)
    (ContactQuotientTransferSupport318.forward c a b d S n I hb hd)=transfer c a d S n I hd :=
  (ContactQuotientTransferIsoInvariant318.transfer_eq c a b d S n I
    (transfer c a b S n I hb) (comparison c a b S n I hb)
    (comparison_projective c a b S n I hb) hd
    (ContactQuotientTransferSupport318.forward c a b d S n I hb hd)).symm
end ContactQuotientTransferCocycle318
