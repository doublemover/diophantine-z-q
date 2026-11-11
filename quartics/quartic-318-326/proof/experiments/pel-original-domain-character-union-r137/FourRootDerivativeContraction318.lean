module
public import FourRootDerivativeFramedLines318
public import FramedLineMorphismContraction318
public section
noncomputable section
namespace FourRootDerivativeContraction318
open AlgebraicGeometry CategoryTheory Opposite
open FourRootGluedScheme318 FourRootActualCanonicalLine318 FourRootDerivativeFramedLines318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
/-- The coefficient is EXTRACTED from the actual universal derivative
and its actual pulled source/intrinsic target frames. No desired zero
ideal or trace-different formula is used in this definition. -/
@[expose] def coefficient(i:Option (Fin 4))(V:(scheme b).Opens)(h:V≤opens b hb i):
    Γ(scheme b,V):=
  FramedLineMorphismCoefficient318.coefficient
    (sourceLine b hb).object (targetLine b hb).object (opens b hb)
    (sourceFrame b hb) (frame b hb) (actualDerivative b hb) i V h
/-- A genuine global contraction from the OPPOSITE derivative line.
The same original derivative, source pullback and intrinsic Omega are
retained. Identification with the actual closed kernel remains a
separate theorem requiring the actual chart coefficient calculation. -/
@[expose] def hom:(idealLineCandidate b hb).object⟶SheafOfModules.unit (scheme b).ringCatSheaf:=
  FramedLineMorphismContraction318.hom
    (sourceLine b hb).object (targetLine b hb).object (opens b hb)
    (sourceFrame b hb) (frame b hb) (actualDerivative b hb) (cover_top b hb)
/-- Actual image on every subordinate open, with the coefficient
computed from the derivative itself; not a support equality. -/
theorem range_on_subopen(i:Option (Fin 4))(V:(scheme b).Opens)(h:V≤opens b hb i):
    LinearMap.range ((hom b hb).val.app (op V)).hom=Ideal.span {coefficient b hb i V h}:=
  FramedLineMorphismContraction318.range_on_subopen
    (sourceLine b hb).object (targetLine b hb).object (opens b hb)
    (sourceFrame b hb) (frame b hb) (actualDerivative b hb) (cover_top b hb) i V h
end FourRootDerivativeContraction318
