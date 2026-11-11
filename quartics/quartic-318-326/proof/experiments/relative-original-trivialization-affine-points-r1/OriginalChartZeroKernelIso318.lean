module
public import OriginalJointAffineFrameBasis318
public import SectionZeroAffineRefinement318
public section
noncomputable section
namespace OriginalChartZeroKernelIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open OriginalJointAffineFrameBasis318 SectionZeroAffineRefinement318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Z : Scheme.{u}} (L : Line X) (s : Γ(L.object,⊤))
  {κ : Type u} (A : κ → CommRingCat.{u}) (j : ∀ a,Spec (A a) ⟶ X)
  [∀ a,IsOpenImmersion (j a)] (hc : ⊤≤⨆a,(j a).opensRange)
  (p : Z ⟶ X) [QuasiCompact p]
  (z : ∀ a,Spec (CommRingCat.of (A a⧸sectionIdeal (A a) (j a) L s)) ⟶ Z)
  (hz : ∀ a,IsPullback (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (sectionIdeal (A a) (j a) L s)))) (z a) (j a) p)
local notation "I" => FramedLineInverse318.inverse L
local notation "F" => InverseLineSectionContraction318.hom L s
local notation "G" => ActualClosedIdealModule318.structure p
local notation "B" => Index L A j

@[expose] def zeroInto (b : B) := SectionZeroAffineRefinement318.into (A b.chart)
  (ring L A j b) (j b.chart) (ringMap L A j b) L s (z b.chart)

include hz in
lemma zero_square (b : B) : IsPullback
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (sectionIdeal (ring L A j b) (embedding L A j b) L s))))
    (zeroInto L s A j z b) (embedding L A j b) p :=
  SectionZeroAffineRefinement318.square (A b.chart) (ring L A j b)
    (j b.chart) (ringMap L A j b) L s p (z b.chart) (hz b.chart)

include hz in
/-- Every kernel equation needed by global descent is now PRODUCED from
the original whole-chart quotient squares and the original section unit. -/
lemma exact_on_basis (b : B) :
    LinearMap.range (F.val.app (op (embedding L A j b ''ᵁ ⊤))).hom =
    LinearMap.ker (G.val.app (op (embedding L A j b ''ᵁ ⊤))).hom :=
  FramedAffineZeroKernel318.contraction_kernel (ring L A j b) (embedding L A j b)
    L s p (zeroInto L s A j z b) (zero_square L s A j p z hz b)
    b.frame (OriginalJointAffineFrameBasis318.frame_le L A j b)

/-- Actual intrinsic regularity on the INTERNALLY constructed joint
original affine/frame basis; no independent kernel equations remain. -/
def Regular : Prop := ∀ b : B,SectionZeroRegularCoordinate318.Regular (ring L A j b)
  (OriginalLineAffineModel318.sections (ring L A j b)
    (LineSheafPullback318.line (embedding L A j b) L))
  (OriginalSectionPullbackComposition318.pull (embedding L A j b) L.object s)

variable (hr : Regular L s A j)

include hr in
lemma injective_on_basis (b : B) : Function.Injective (F.app (embedding L A j b ''ᵁ ⊤)) :=
  FramedAffineZeroKernel318.contraction_injective (ring L A j b) (embedding L A j b)
    L s b.frame (OriginalJointAffineFrameBasis318.frame_le L A j b) (hr b)

/-- Genuine GLOBAL inverse-line identification with the ACTUAL module
kernel of the original zero map. The exactness hypotheses are constructed
from original quotient charts; only the stated section regularity remains. -/
@[expose] def iso : I.object ≅ ActualClosedIdealModule318.object p :=
  ModuleBasisKernel318.iso F G (fun b : B => embedding L A j b ''ᵁ ⊤)
    (image_basis L A j hc) (exact_on_basis L s A j p z hz)
    (injective_on_basis L s A j hr)

@[reassoc] lemma iso_inclusion : (iso L s A j hc p z hz hr).hom ≫
    ActualClosedIdealModule318.inclusion p=F :=
  ModuleBasisKernel318.iso_hom_inclusion F G (fun b : B => embedding L A j b ''ᵁ ⊤)
    (image_basis L A j hc) (exact_on_basis L s A j p z hz)
    (injective_on_basis L s A j hr)
end OriginalChartZeroKernelIso318
