module
public import SectionZeroCartierKernel318
public import CartierCanonicalZeroCharts318
public section
noncomputable section
namespace CartierDivisorLineBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
universe u
variable {Z X W Y B T : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ B) [hflat : Flat (p ≫ a)] (f : T ⟶ B)
  (q : W ⟶ Y) [IsClosedImmersion q] (t : W ⟶ Z) (g : Y ⟶ X) (b : Y ⟶ T)
  (F : IsPullback t q p g) (K : IsPullback g b a f)
  (hp : OriginalRegularClosedCharts318.Property p)
include F K hflat hp in
lemma regular : OriginalRegularClosedCharts318.Property q :=
  RelativeCartierSchemeCartesian318.regular p a f q t g b F K hp
local notation "D" => CartierCanonicalSection318.divisorLine p hp
local notation "s" => CartierCanonicalSection318.section p hp
local notation "L" => LineSheafPullback318.line g D
local notation "s'" => OriginalSectionPullbackComposition318.pull g D.object s
/-- Actual full zero charts of the genuine pulled original O(D) section. -/
@[expose] def zeroCharts : SectionZeroChartData318.Data q L s' :=
  SectionZeroPullbackData318.data p q t g F D s (CartierCanonicalZeroCharts318.data p hp)
/-- The inverse of the actual pulled O(D) is the new ACTUAL kernel
sheaf. The full inclusion is retained as contraction by the actual
geometric pullback section, not an unrelated isomorphic line. -/
@[expose] def kernelIso : (FramedLineInverse318.inverse L).object ≅ ActualClosedIdealModule318.object q :=
  SectionZeroCartierKernel318.iso q L s' (zeroCharts p q t g F hp)
    (regular p a f q t g b F K hp)
@[reassoc] lemma kernel_inclusion : (kernelIso p a f q t g b F K hp).hom ≫
    ActualClosedIdealModule318.inclusion q=InverseLineSectionContraction318.hom L s' :=
  SectionZeroCartierKernel318.inclusion q L s' (zeroCharts p q t g F hp)
    (regular p a f q t g b F K hp)
/-- Genuine O(D) compatibility with EVERY coefficient scheme change. -/
lemma divisor_class : classOf (CartierCanonicalSection318.divisorLine q (regular p a f q t g b F K hp))=
    classOf L :=
  SectionZeroCartierKernel318.divisor_class q L s' (zeroCharts p q t g F hp)
    (regular p a f q t g b F K hp)
@[expose] def divisorIso :
    (CartierCanonicalSection318.divisorLine q (regular p a f q t g b F K hp)).object ≅ L.object :=
  Classical.choice ((LineSheafClass318.classOf_eq_iff _ _).mp (divisor_class p a f q t g b F K hp))
end CartierDivisorLineBaseChange318
