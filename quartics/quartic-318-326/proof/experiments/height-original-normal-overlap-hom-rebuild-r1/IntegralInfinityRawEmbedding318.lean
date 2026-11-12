module
public import IntegralInfinitySourceParameters318
public import PerfectCoefficientFrameTransport318
public import OriginalNormalInfinityDuality318
public section
noncomputable section
namespace IntegralInfinityRawEmbedding318
open Polynomial IntegralDistinctContactOpen318 IntegralInfinitySourceParameters318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local notation "A" => DVRNormalizedInfinityOrder318.Order R d a
local instance : Algebra P F := IntegralInfinityReciprocalScalar318.baseAlgebra R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : IsScalarTower P F B := IntegralInfinityReciprocalScalar318.tower R a d

@[expose] def rawMap : A →ₐ[P] B :=
  ((sourceEquiv R a d).toAlgHom.restrictScalars P).comp
    (FourRootSignBaseChange318.coefficientMap (DVRNormalizedInfinityOrder318.coefficient R d a) F)

lemma rawMap_root (i : Fin 4) : rawMap R a d
    (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient R d a) i)=
      (↑(parameterUnit R a d)⁻¹:F) •
        FourRootOrderSigns318.generator (finiteParameter R a d) i := by
  change sourceEquiv R a d
    (FourRootSignBaseChange318.coefficientMap _ F (FourRootOrderSigns318.generator _ i))=_
  rw [FourRootSignBaseChange318.coefficientMap_generator,sourceEquiv_root]

/-- The source frame is transported through the actual scaled-root
algebra equivalence, not chosen by its rank. -/
@[expose] def frame : TensorCoefficientDuality318.Frame F B FourRootIntegralDuality318.Index :=
  PerfectCoefficientFrameTransport318.frame
    (FourRootIntegralDuality318.frame (infinityParameter R a d)) (sourceEquiv R a d)

lemma basis (i : FourRootIntegralDuality318.Index) : rawMap R a d
    ((FourRootIntegralDuality318.frame (DVRNormalizedInfinityOrder318.coefficient R d a)).basis i)=
      (frame R a d).basis i := by
  change sourceEquiv R a d (FourRootSignBaseChange318.coefficientMap _ F
    ((FourRootIntegralDuality318.frame _).basis i))=_
  rw [FourRootDualityBaseChange318.coefficientMap_basis]
  rfl

lemma coefficient (x : A) : (frame R a d).coefficient (rawMap R a d x)=
    algebraMap P F (FourRootIntegralDuality318.coefficient
      (DVRNormalizedInfinityOrder318.coefficient R d a) x) := by
  change (PerfectCoefficientFrameTransport318.frame _ (sourceEquiv R a d)).coefficient
    (sourceEquiv R a d (FourRootSignBaseChange318.coefficientMap _ F x))=_
  rw [PerfectCoefficientFrameTransport318.coefficient]
  exact FourRootDualityBaseChange318.coefficientMap_coefficient _ x

variable [IsDomain R] [CharZero R] (hd : ∀ i,d i ≠ 0)
include hd in
lemma base_injective : Function.Injective (algebraMap P F) := by
  letI := IntegralInfinityReciprocalScalar318.localization R a d
  exact IntegralInfinityArithmeticDomain318.away_injective P F
    (IntegralReciprocalBase318.reciprocalDenominator R a (arithmeticDenominator R d))
    (IntegralReciprocalBase318.reciprocalDenominator_ne_zero R a _
      (arithmeticDenominator_ne_zero R d hd))

include hd in
lemma injective : Function.Injective (rawMap R a d) := by
  letI : Module.Free P A := (DVRNormalizedInfinityOrder318.finite_free R d a).2
  exact (sourceEquiv R a d).injective.comp
    ((FourRootOrder318.baseChange (DVRNormalizedInfinityOrder318.coefficient R d a) F).injective.comp
      (Algebra.TensorProduct.includeRight_injective (R:=P) (A:=F) (B:=A)
        (base_injective R a d hd)))
end IntegralInfinityRawEmbedding318
