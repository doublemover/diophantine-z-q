module
public import ContactRelativeOriginalTwistIso318
public import ContactRelativeFixedPowerVanishing318
public import ContactOriginalPositiveProjectiveComparison318
public import OriginalTensorPowerCongr318
public import LineFrameIsoTransport318
public section
noncomputable section
namespace ContactRelativeProjectivePositive318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactRelativeOriginalProjection318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)

/-- The ORIGINAL contact-to-projective-line map after the actual p-first
coefficient base change, not the unrelated level-three j-map. -/
@[expose] def projectiveMap := projection R c ≫ ContactBicanonicalProjectiveMap318.projectiveMap c

@[expose] def object : (curve R c).Modules :=
  (Scheme.Modules.pullback (projectiveMap R c)).obj ProjectiveLineOOne318.line

/-- Actual projective O(1) pullback is the SAME fixed relative geometric
line used in the eventual H1 theorem. Original associators, rational
projective comparison, and full relative chart comparisons are retained. -/
@[expose] def iso : object R c ≅ (ContactRelativeGeometricTwist318.line R c 1).object :=
  ((Scheme.Modules.pullbackComp (projection R c)
    (ContactBicanonicalProjectiveMap318.projectiveMap c)).app ProjectiveLineOOne318.line).symm ≪≫
  (Scheme.Modules.pullback (projection R c)).mapIso
    (ContactOriginalPositiveProjectiveComparison318.iso c) ≪≫
  ContactRelativeOriginalTwistIso318.iso R c 1

/-- Genuine frames on the actual projective pullback object, transported
through its specified original sheaf isomorphism, not a renamed twist. -/
@[expose] def line : Line (curve R c) where
  object := object R c
  Index := ULift Bool
  opens := (ContactRelativeGeometricTwist318.line R c 1).opens
  cover := (ContactRelativeGeometricTwist318.line R c 1).cover
  frame i := LineFrameIsoTransport318.transported (iso R c).symm
    ((ContactRelativeGeometricTwist318.line R c 1).opens i)
    ((ContactRelativeGeometricTwist318.line R c 1).frame i)

@[expose] def powerIso (n : ℕ) :
    (LineSheafTensorPower318.line (line R c) n).object ≅
    (LineSheafTensorPower318.line (ContactRelativeGeometricTwist318.line R c 1) n).object :=
  OriginalTensorPowerCongr318.iso (iso R c) n

@[expose] def twistedPowerIso (L : Line (curve R c)) (n : ℕ) :
    (LineSheafTensor318.line L (LineSheafTensorPower318.line (line R c) n)).object ≅
    (ContactRelativeFixedPowerVanishing318.twistedPower R c L n).object :=
  TensorSheafFunctor318.congr (Iso.refl L.object) (powerIso R c n)
end ContactRelativeProjectivePositive318
