module
public import FourRootGlobalRelativeCotangent318
public import FourRootDerivativeFramedLines318
public import AffineCokernelSections318
public section
noncomputable section
namespace FourRootAffineCotangentSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
open FourRootProjectiveDifferential318 FourRootDerivativeFramedLines318
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)

@[expose] def finiteSourceFrame (i : Fin 4) :
    SheafOfModules.unit (Spec (CommRingCat.of (FiniteRing b i))).ringCatSheaf ≅
      (sourceObject b).restrict (finiteEmbedding b i) :=
  AffineCokernelSections318.chartFrame (finiteEmbedding b i) (sourceObject b)
    (sourceFrame b hb (some i))

@[expose] def infinitySourceFrame :
    SheafOfModules.unit (Spec (CommRingCat.of (InfinityRing b hb))).ringCatSheaf ≅
      (sourceObject b).restrict (infinityEmbedding b hb) :=
  AffineCokernelSections318.chartFrame (infinityEmbedding b hb) (sourceObject b)
    (sourceFrame b hb none)

abbrev finiteSectionQuotient (i : Fin 4) :=
  AffineCokernelSections318.sectionQuotient
    ((Scheme.Modules.restrictFunctor (finiteEmbedding b i)).map (derivative b))
abbrev infinitySectionQuotient :=
  AffineCokernelSections318.sectionQuotient
    ((Scheme.Modules.restrictFunctor (infinityEmbedding b hb)).map (derivative b))

/-- The SAME global intrinsic relative cotangent sheaf, restricted to
EVERY actual finite root chart, is tilde of the actual sections cokernel.
The section map here is obtained from the original sheaf derivative. -/
@[expose] def finiteIso (i : Fin 4) :
    (FourRootGlobalRelativeCotangent318.omega b).restrict (finiteEmbedding b i) ≅
      tilde (R := CommRingCat.of (FiniteRing b i))
        (ModuleCat.of (FiniteRing b i) (finiteSectionQuotient b i)) := by
  letI := AffineCokernelSections318.counit_isIso_of_frame
    ((sourceObject b).restrict (finiteEmbedding b i)) (finiteSourceFrame b hb i)
  letI := AffineCokernelSections318.counit_isIso_of_frame
    ((FourRootIntrinsicCanonicalFrames318.omega b).restrict (finiteEmbedding b i))
    (FourRootWholeCanonicalCover318.localFrame b hb (some i)).symm
  exact AffineCokernelSections318.restrictionIso (finiteEmbedding b i) (derivative b)

/-- Infinity retains the actual reciprocal-base derivative and original
canonical chart. No meromorphic dt or rank-eight u-base is substituted. -/
@[expose] def infinityIso :
    (FourRootGlobalRelativeCotangent318.omega b).restrict (infinityEmbedding b hb) ≅
      tilde (R := CommRingCat.of (InfinityRing b hb))
        (ModuleCat.of (InfinityRing b hb) (infinitySectionQuotient b hb)) := by
  letI := AffineCokernelSections318.counit_isIso_of_frame
    ((sourceObject b).restrict (infinityEmbedding b hb)) (infinitySourceFrame b hb)
  letI := AffineCokernelSections318.counit_isIso_of_frame
    ((FourRootIntrinsicCanonicalFrames318.omega b).restrict (infinityEmbedding b hb))
    (FourRootWholeCanonicalCover318.localFrame b hb none).symm
  exact AffineCokernelSections318.restrictionIso (infinityEmbedding b hb) (derivative b)
end FourRootAffineCotangentSections318
