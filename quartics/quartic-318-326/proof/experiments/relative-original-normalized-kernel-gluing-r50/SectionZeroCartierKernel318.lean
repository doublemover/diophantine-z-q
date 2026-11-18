module
public import SectionZeroPullbackData318
public import OriginalCartierZeroKernelIso318
public section
noncomputable section
namespace SectionZeroCartierKernel318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (L : Line X) (s : Γ(L.object,⊤)) (D : SectionZeroChartData318.Data p L s)
  (hp : OriginalRegularClosedCharts318.Property p)
/-- Actual inverse-line/sheaf-kernel comparison from complete original
section-zero charts and genuine Cartier regularity of that same family. -/
@[expose] def iso : (FramedLineInverse318.inverse L).object ≅ ActualClosedIdealModule318.object p :=
  OriginalCartierZeroKernelIso318.iso L s D.ring D.into D.cover p D.zero D.cartesian hp
@[reassoc] lemma inclusion : (iso p L s D hp).hom ≫ ActualClosedIdealModule318.inclusion p=
    InverseLineSectionContraction318.hom L s :=
  OriginalCartierZeroKernelIso318.iso_inclusion L s D.ring D.into D.cover p D.zero D.cartesian hp
include D in
/-- The original divisor line is recovered, not only its zero support. -/
lemma divisor_class : classOf (CartierCanonicalSection318.divisorLine p hp)=classOf L := by
  have he : classOf (FramedLineInverse318.inverse L)=
      classOf (ActualCartierIdealLine318.line p hp) := LineSheafClass318.classOf_eq (iso p L s D hp)
  change classOf (FramedLineInverse318.inverse (ActualCartierIdealLine318.line p hp))=classOf L
  rw [LineSheafClassGroup318.classOf_inverse,← he,LineSheafClassGroup318.classOf_inverse,inv_inv]
end SectionZeroCartierKernel318
