module
public import FourRootWholeDerivativeDifferent318
public import LinePullbackFrames318
public import OpenLineFrameRefinement318
public import LineSheafTensor318
public import FramedLineInverse318
public section
noncomputable section
namespace FourRootDerivativeFramedLines318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open FourRootGluedScheme318 FourRootProjectiveDifferential318
open FourRootActualCanonicalLine318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
@[expose] def baseOpen:Option (Fin 4)→Base.Opens
  | none=>(infinityBaseChart b).opensRange
  | some _=>finiteBaseChart.opensRange
@[expose] def baseFrame(i:Option (Fin 4)):
    SheafOfModules.unit (baseOpen b i).toScheme.ringCatSheaf≅
      baseOmega.restrict (baseOpen b i).ι:=by
  cases i with
  | none=>exact ActualOpenImmersionLineFrame318.ambientFrame (infinityBaseChart b) baseOmega
      ((Scheme.Modules.restrictUnitIso (infinityBaseChart b)).symm≪≫infinityBaseFrame b)
  | some i=>exact ActualOpenImmersionLineFrame318.ambientFrame finiteBaseChart baseOmega
      ((Scheme.Modules.restrictUnitIso finiteBaseChart).symm≪≫finiteBaseFrame)
lemma source_open_le(i:Option (Fin 4)):
    opens b hb i≤FourRootProjectiveProjection318.projection b ⁻¹ᵁbaseOpen b i:=by
  cases i with
  | none=>
    simpa only [opens,FourRootWholeCanonicalCover318.embedding,baseOpen,
      Scheme.Hom.image_top_eq_opensRange] using
      FourRootProjectiveDifferentialCharts318.infinity_preimage b hb
  | some i=>
    simpa only [opens,FourRootWholeCanonicalCover318.embedding,baseOpen,
      Scheme.Hom.image_top_eq_opensRange] using
      FourRootProjectiveDifferentialCharts318.finite_preimage b i
@[expose] def sourceObject:(scheme b).Modules:=
  (Scheme.Modules.pullback (FourRootProjectiveProjection318.projection b)).obj baseOmega
/-- Genuine frames of the ACTUAL pullback cotangent line on the already
proved five-chart source cover. No abstract line with the same degree
or cocycle is substituted for the derivative's original domain. -/
@[expose] def sourceFrame(i:Option (Fin 4)):
    SheafOfModules.unit (opens b hb i).toScheme.ringCatSheaf≅
      (sourceObject b).restrict (opens b hb i).ι:=
  OpenLineFrameRefinement318.frame (sourceObject b)
    (FourRootProjectiveProjection318.projection b ⁻¹ᵁbaseOpen b i)
    (LinePullbackFrames318.frame (FourRootProjectiveProjection318.projection b)
      baseOmega (baseOpen b i) (baseFrame b i))
    (opens b hb i) (source_open_le b hb i)
@[expose] def sourceLine:Line (scheme b) where
  object:=sourceObject b
  Index:=Option (Fin 4)
  opens:=opens b hb
  cover:=cover_top b hb
  frame:=sourceFrame b hb
@[expose] def targetLine:Line (scheme b):=canonicalLine b hb
/-- The genuine derivative already constructed has exactly these two
actual framed objects as its domain and codomain. -/
@[expose] def actualDerivative:(sourceLine b hb).object⟶(targetLine b hb).object:=
  derivative b
/-- Positive Hom-line orientation: L^{-1} tensor M for d:L->M. -/
@[expose] def homLine:Line (scheme b):=
  LineSheafTensor318.line (FramedLineInverse318.inverse (sourceLine b hb)) (targetLine b hb)
/-- The ideal must compare with the OPPOSITE line M^{-1} tensor L.
It is not identified with the positive Hom-line, the source line, or
Omega itself before the actual contraction/kernel proof. -/
@[expose] def idealLineCandidate:Line (scheme b):=
  LineSheafTensor318.line (FramedLineInverse318.inverse (targetLine b hb)) (sourceLine b hb)
end FourRootDerivativeFramedLines318
