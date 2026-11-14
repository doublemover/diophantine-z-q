module
public import FourRootAffineCotangentSections318
public import FourRootDerivativeCoefficientIdeals318
public import FourRootDerivativeZeroCotangent318
public import AffineSectionFrames318
public section
noncomputable section
namespace FourRootAffineCotangentIdeal318
open AlgebraicGeometry CategoryTheory Opposite
open FourRootIntrinsicCanonicalFrames318 FourRootDerivativeFramedLines318
open FourRootDerivativeCoefficientIdeals318 FourRootAffineCotangentSections318
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)

abbrev finiteOpen (i : Fin 4) := finiteEmbedding b i ''ᵁ ⊤
abbrev infinityOpen := infinityEmbedding b hb ''ᵁ ⊤
lemma finite_le (i : Fin 4) : finiteOpen b i ≤ FourRootActualCanonicalLine318.opens b hb (some i) := by
  simp only [finiteOpen,FourRootActualCanonicalLine318.opens,
    FourRootWholeCanonicalCover318.embedding,Scheme.Hom.image_top_eq_opensRange,le_refl]
lemma infinity_le : infinityOpen b hb ≤ FourRootActualCanonicalLine318.opens b hb none := by
  simp only [infinityOpen,FourRootActualCanonicalLine318.opens,
    FourRootWholeCanonicalCover318.embedding,Scheme.Hom.image_top_eq_opensRange,le_refl]

lemma finite_literal (i : Fin 4) :
    literal b hb (some i) (finiteOpen b i) (finite_le b hb i) =
      AffineSectionFrames318.scalars (finiteEmbedding b i)
        (2*FourRootActualBranchKaehler318.sourceCoordinate b i) := by
  simp only [literal,finiteOpen,homOfLE_refl,op_id,Functor.map_id]
  rfl
lemma infinity_literal :
    literal b hb none (infinityOpen b hb) (infinity_le b hb) =
      AffineSectionFrames318.scalars (infinityEmbedding b hb)
        (2*FourRootActualInfinityKaehler318.coordinate b hb) := by
  simp only [literal,infinityOpen,homOfLE_refl,op_id,Functor.map_id]
  rfl

/-- The actual affine section-map quotient is identified with the SAME
whole zero ideal restricted along the original canonical localization.
Both source and target generator units were proved from actual sheaf frames. -/
@[expose] def finiteQuotientEquiv (i : Fin 4) :
    finiteSectionQuotient b i ≃ₗ[FiniteRing b i]
      FiniteRing b i ⧸ FourRootDerivativeZeroCotangent318.finiteZeroIdeal b i := by
  let e := OpenLineFrameCoordinates318.frame (sourceObject b)
    (FourRootActualCanonicalLine318.opens b hb (some i)) (sourceFrame b hb (some i))
    (finiteOpen b i) (finite_le b hb i)
  let f := OpenLineFrameCoordinates318.frame (omega b)
    (FourRootActualCanonicalLine318.opens b hb (some i)) (FourRootActualCanonicalLine318.frame b hb (some i))
    (finiteOpen b i) (finite_le b hb i)
  have him := image b hb (some i) (finiteOpen b i) (finite_le b hb i)
  rw [finite_literal] at him
  exact (AffineSectionFrames318.quotientEquiv (finiteEmbedding b i)
    (FourRootProjectiveDifferential318.derivative b) e f
    (sourceTest b hb (some i) (finiteOpen b i) (finite_le b hb i))
    (targetTest b hb (some i) (finiteOpen b i) (finite_le b hb i))
    (2*FourRootActualBranchKaehler318.sourceCoordinate b i) him
    (source_unit b hb (some i) (finiteOpen b i) (finite_le b hb i))
    (target_unit b hb (some i) (finiteOpen b i) (finite_le b hb i))).trans
      (Submodule.quotEquivOfEq _ _ (FourRootDerivativeFiniteIdeal318.derivative_ideal b i).symm)

@[expose] def infinityQuotientEquiv :
    infinitySectionQuotient b hb ≃ₗ[InfinityRing b hb]
      InfinityRing b hb ⧸ FourRootDerivativeZeroCotangent318.infinityZeroIdeal b hb := by
  let e := OpenLineFrameCoordinates318.frame (sourceObject b)
    (FourRootActualCanonicalLine318.opens b hb none) (sourceFrame b hb none)
    (infinityOpen b hb) (infinity_le b hb)
  let f := OpenLineFrameCoordinates318.frame (omega b)
    (FourRootActualCanonicalLine318.opens b hb none) (FourRootActualCanonicalLine318.frame b hb none)
    (infinityOpen b hb) (infinity_le b hb)
  have him := image b hb none (infinityOpen b hb) (infinity_le b hb)
  rw [infinity_literal] at him
  exact (AffineSectionFrames318.quotientEquiv (infinityEmbedding b hb)
    (FourRootProjectiveDifferential318.derivative b) e f
    (sourceTest b hb none (infinityOpen b hb) (infinity_le b hb))
    (targetTest b hb none (infinityOpen b hb) (infinity_le b hb))
    (2*FourRootActualInfinityKaehler318.coordinate b hb) him
    (source_unit b hb none (infinityOpen b hb) (infinity_le b hb))
    (target_unit b hb none (infinityOpen b hb) (infinity_le b hb))).trans
      (Submodule.quotEquivOfEq _ _ (FourRootDerivativeInfinityIdeal318.derivative_ideal b hb).symm)

/-- Actual local isomorphism on every original finite canonical chart.
The quotient ideal is the mapped full derivative-zero/trace-different ideal,
not its radical, support, or an ideal guessed from ramification numbers. -/
@[expose] def finiteIso (i : Fin 4) :
    (FourRootGlobalRelativeCotangent318.omega b).restrict (finiteEmbedding b i) ≅
      tilde (R := CommRingCat.of (FiniteRing b i)) (ModuleCat.of (FiniteRing b i)
        (FiniteRing b i ⧸ FourRootDerivativeZeroCotangent318.finiteZeroIdeal b i)) :=
  FourRootAffineCotangentSections318.finiteIso b hb i ≪≫
    (tilde.functor (CommRingCat.of (FiniteRing b i))).mapIso (finiteQuotientEquiv b hb i).toModuleIso

/-- Same actual sheaf comparison on the whole canonical infinity chart,
retaining all infinity centers and the original reciprocal base v=u². -/
@[expose] def infinityIso :
    (FourRootGlobalRelativeCotangent318.omega b).restrict (infinityEmbedding b hb) ≅
      tilde (R := CommRingCat.of (InfinityRing b hb)) (ModuleCat.of (InfinityRing b hb)
        (InfinityRing b hb ⧸ FourRootDerivativeZeroCotangent318.infinityZeroIdeal b hb)) :=
  FourRootAffineCotangentSections318.infinityIso b hb ≪≫
    (tilde.functor (CommRingCat.of (InfinityRing b hb))).mapIso (infinityQuotientEquiv b hb).toModuleIso
end FourRootAffineCotangentIdeal318
