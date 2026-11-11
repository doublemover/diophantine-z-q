module
public import AffineZeroKernelRestriction318
public import OriginalAffineOpenFrame318
public import OriginalAffineSectionZero318
public import SectionZeroRegularCoordinate318
public import InverseLineSectionContraction318
public section
noncomputable section
namespace FramedAffineZeroKernel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open AffineQuotientKernelSections318 AffineZeroKernelRestriction318
open OriginalAffineOpenFrame318 OriginalOpenPullbackSections318 ModuleLocalGluing318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A : CommRingCat.{u}) {X Z : Scheme.{u}} (j : Spec A ⟶ X) [IsOpenImmersion j]
  (L : Line X) (s : Γ(L.object,⊤))
local notation "U" => j ''ᵁ ⊤
local notation "N" => LineSheafPullback318.line j L
local notation "t" => sectionPull j L.object s
local notation "J" => OriginalAffineSectionZero318.ideal A N t
variable (e : Γ(L.object,U) ≃ₗ[Γ(X,U)] Γ(X,U))

lemma frame_section : frame A j L e t =
    ringEquivalence A j (e (res L.object (show U≤⊤ from le_top) s)) := by
  change ringEquivalence A j (e (sectionsEquiv j L.object t))=_
  rw [unit_sections]
  rfl

lemma coefficient_ring (a : Γ(X,U)) :
    coefficient A j (ringEquivalence A j a)=a := by
  change (ringEquivalence A j).symm (ringEquivalence A j a)=a
  exact RingEquiv.symm_apply_apply (ringEquivalence A j) a

/-- Actual affine evaluation ideal in the original ambient frame. This
uses the genuine pullback UNIT and its proven ambient restriction formula. -/
lemma coordinate_ideal : Ideal.map (coefficient A j).hom J =
    Ideal.span {e (res L.object (show U≤⊤ from le_top) s)} := by
  have he : J=Ideal.span {frame A j L e t} :=
    SectionZeroRegularCoordinate318.ideal_in_frame A
      (OriginalLineAffineModel318.sections A N) t (frame A j L e)
  rw [he,Ideal.map_span,Set.image_singleton,frame_section,coefficient_ring]

variable (p : Z ⟶ X) [QuasiCompact p]
  (k : Spec (CommRingCat.of (A⧸J)) ⟶ Z)
  (hs : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) k j p)

include hs in
/-- The literal kernel of the SAME global zero map is the principal
ideal of the SAME original ambient section coordinate. -/
lemma kernel_coordinate : RingHom.ker (p.app U).hom =
    Ideal.span {e (res L.object (show U≤⊤ from le_top) s)} := by
  rw [← p.ker_apply (chartOpen A j),chart_kernel A J p j k hs]
  exact coordinate_ideal A j L s e

/-- Regularity transports through the actual scalar isomorphism and
actual original pullback frame; it is not inferred from vanishing sets. -/
lemma coordinate_regular
    (hr : SectionZeroRegularCoordinate318.Regular A
      (OriginalLineAffineModel318.sections A N) t) :
    ∀ a : Γ(X,U),a * e (res L.object (show U≤⊤ from le_top) s)=0 → a=0 := by
  have h := (SectionZeroRegularCoordinate318.regular_iff A
    (OriginalLineAffineModel318.sections A N) t (frame A j L e)).mp hr
  intro a ha
  apply (ringEquivalence A j).injective
  rw [map_zero]
  apply h
  rw [frame_section,← map_mul,ha,map_zero]

variable (i : L.Index) (hU : U≤L.opens i)
local notation "E" => InverseLineSectionContraction318.coordinate L i U hU

include hs in
/-- At a genuine original frame chart the producer matches precisely
the contraction map used in the global inverse-line construction. -/
lemma contraction_kernel :
    LinearMap.range ((InverseLineSectionContraction318.hom L s).val.app (op U)).hom =
    LinearMap.ker ((ActualClosedIdealModule318.structure p).val.app (op U)).hom := by
  rw [InverseLineSectionContraction318.range_on_subopen L s i U hU]
  rw [ActualClosedIdealModule318.section_kernel]
  exact (kernel_coordinate A j L s E p k hs).symm

lemma contraction_injective
    (hr : SectionZeroRegularCoordinate318.Regular A
      (OriginalLineAffineModel318.sections A N) t) :
    Function.Injective ((InverseLineSectionContraction318.hom L s).app U) :=
  InverseLineSectionContraction318.injective_on_subopen L s i U hU
    (coordinate_regular A j L s E hr)
end FramedAffineZeroKernel318
