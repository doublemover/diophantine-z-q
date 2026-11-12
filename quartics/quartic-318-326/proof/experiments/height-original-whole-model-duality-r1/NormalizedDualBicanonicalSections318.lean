module
public import NormalizedCanonicalTensorTransition318
public import FourRootDualScalarExtension318
public section
noncomputable section
namespace NormalizedDualBicanonicalSections318
open Polynomial NormalizedReciprocalLaurent318 NormalizedWholeOverlap318
open FiniteDualTransport318
set_option maxHeartbeats 2200000
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)
@[expose] def constant : R := 256*∏ i : Fin 4,d i
@[expose] def finite0 : R[X] := C (constant R d)
@[expose] def finite1 : R[X] := X*C (constant R d)
@[expose] def infinity0 : R[X] := C (constant R d)*X^4
@[expose] def infinity1 : R[X] := C (constant R d)*X^3

@[expose] def finiteSection (p : R[X]) :
    Square (R:=R[X]) (A:=FiniteOrder R d a) :=
  squareFrame (FourRootIntegralDuality318.frame (DVRNormalizedFiniteOrder318.coefficient R d a))
    (algebraMap R[X] (FiniteOrder R d a) p)
@[expose] def infinitySection (p : R[X]) :
    Square (R:=R[X]) (A:=InfinityOrder R d a) :=
  squareFrame (FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient R d a))
    (algebraMap R[X] (InfinityOrder R d a) p)

/-- Actual balanced extension from the integral finite-chart tensor module. -/
@[expose] def finiteExtension : Square (R:=R[X]) (A:=FiniteOrder R d a) →ₛₗ[
    (FourRootSignBaseChange318.coefficientMap (DVRNormalizedFiniteOrder318.coefficient R d a)
      (Laurent R)).toRingHom]
    Square (R:=Laurent R) (A:=FourRootOrder318.Order (finiteParameter R d a)) :=
  FourRootDualScalarExtension318.squareMap (S:=Laurent R)
    (DVRNormalizedFiniteOrder318.coefficient R d a)

theorem finiteExtension_section (p : R[X]) : finiteExtension R d a (finiteSection R d a p)=
    squareFrame (FourRootIntegralDuality318.frame (finiteParameter R d a))
      (algebraMap (Laurent R) _ (algebraMap R[X] (Laurent R) p)) := by
  rw [finiteExtension,finiteSection,FourRootDualScalarExtension318.squareMap_frame,
    AlgHom.commutes,IsScalarTower.algebraMap_apply R[X] (Laurent R)]

/-- The reciprocal scalar action is installed only in this definition;
its whole target is the actual infinity-parameter order on the same Laurent base. -/
@[expose] def infinityExtension : Square (R:=R[X]) (A:=InfinityOrder R d a) →
    Square (R:=Laurent R) (A:=FourRootOrder318.Order (infinityParameter R d a)) := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R).toRingHom.toAlgebra
  exact FourRootDualScalarExtension318.squareMap (S:=Laurent R)
    (DVRNormalizedInfinityOrder318.coefficient R d a)

theorem infinityExtension_section (p : R[X]) : infinityExtension R d a (infinitySection R d a p)=
    squareFrame (FourRootIntegralDuality318.frame (infinityParameter R d a))
      (algebraMap (Laurent R) _ (reciprocalMap R p)) := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R).toRingHom.toAlgebra
  change FourRootDualScalarExtension318.squareMap (S:=Laurent R)
    (DVRNormalizedInfinityOrder318.coefficient R d a)
      (squareFrame _ (algebraMap R[X] (InfinityOrder R d a) p))=_
  rw [FourRootDualScalarExtension318.squareMap_frame,AlgHom.commutes,
    IsScalarTower.algebraMap_apply R[X] (Laurent R)] <;> rfl

/-- The two original candidate sections are honest integral tensor
sections of the actual finite-dual modules, without any denominator or
bad-prime unit hypothesis. -/
@[expose] def section0Finite := finiteSection R d a (finite0 R d)
@[expose] def section1Finite := finiteSection R d a (finite1 R d)
@[expose] def section0Infinity := infinitySection R d a (infinity0 R d)
@[expose] def section1Infinity := infinitySection R d a (infinity1 R d)

lemma coefficient_overlap0 :
    algebraMap R[X] (Laurent R) (finite0 R d)*(↑(coordinate R)⁻¹:Laurent R)^4=
      reciprocalMap R (infinity0 R d) := by
  simp [finite0,infinity0,reciprocalMap,Polynomial.aeval_C,Polynomial.aeval_X,
    ←IsScalarTower.algebraMap_apply R R[X] (Laurent R)]

lemma coefficient_overlap1 :
    algebraMap R[X] (Laurent R) (finite1 R d)*(↑(coordinate R)⁻¹:Laurent R)^4=
      reciprocalMap R (infinity1 R d) := by
  have hu : (coordinate R:Laurent R)*(↑(coordinate R)⁻¹:Laurent R)=1 := Units.mul_inv _
  simp only [finite1,infinity1,map_mul,map_pow,←coordinate_value,
    ←IsScalarTower.algebraMap_apply R R[X] (Laurent R),reciprocalMap,
    Polynomial.aeval_C,Polynomial.aeval_X]
  calc
    _ = algebraMap R (Laurent R) (constant R d)*
      ((coordinate R:Laurent R)*(↑(coordinate R)⁻¹:Laurent R))*(↑(coordinate R)⁻¹:Laurent R)^3 := by ring
    _ = _ := by rw [hu,mul_one]

/-- Whole-order overlap equality for every pair of polynomial
coefficients satisfying the explicit Laurent identity. This is applied
below to both original power4/power3 section coefficients. -/
theorem overlap (p q : R[X])
    (hpq : algebraMap R[X] (Laurent R) p*(↑(coordinate R)⁻¹:Laurent R)^4=reciprocalMap R q) :
    NormalizedCanonicalTensorTransition318.canonicalSquare R d a
      (squareFrame (FourRootIntegralDuality318.frame (finiteParameter R d a))
        (algebraMap (Laurent R) _ (algebraMap R[X] (Laurent R) p))) =
      squareFrame (FourRootIntegralDuality318.frame (infinityParameter R d a))
        (algebraMap (Laurent R) _ (reciprocalMap R q)) := by
  rw [NormalizedCanonicalTensorTransition318.canonicalSquare_frame,AlgEquiv.commutes,←map_mul,hpq]

/-- Genuine equality of the images of the two literal integral sections,
not an equality of formulas on chosen pure-tensor presentations alone. -/
theorem section0_overlap :
    NormalizedCanonicalTensorTransition318.canonicalSquare R d a
      (finiteExtension R d a (section0Finite R d a))=
      infinityExtension R d a (section0Infinity R d a) := by
  rw [section0Finite,section0Infinity,finiteExtension_section,infinityExtension_section]
  exact overlap R d a (finite0 R d) (infinity0 R d) (coefficient_overlap0 R d)

theorem section1_overlap :
    NormalizedCanonicalTensorTransition318.canonicalSquare R d a
      (finiteExtension R d a (section1Finite R d a))=
      infinityExtension R d a (section1Infinity R d a) := by
  rw [section1Finite,section1Infinity,finiteExtension_section,infinityExtension_section]
  exact overlap R d a (finite1 R d) (infinity1 R d) (coefficient_overlap1 R d)
end NormalizedDualBicanonicalSections318
