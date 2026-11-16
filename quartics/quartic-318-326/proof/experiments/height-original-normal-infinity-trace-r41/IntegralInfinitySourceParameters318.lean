module
public import IntegralInfinityReciprocalScalar318
public import DVRNormalizedInfinityOrder318
public import FourRootUnitScale318
public section
noncomputable section
namespace IntegralInfinitySourceParameters318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] (a d : Fin 4 → R)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "δ" => arithmeticDenominator R d
@[expose] def finiteParameter (i : Fin 4) : F :=
  algebraMap P F (DistinctContactIntegralDomain318.coefficient R a d i)
@[expose] def infinityParameter (i : Fin 4) : F :=
  IntegralInfinityReciprocalScalar318.baseMap R a d (DVRNormalizedInfinityOrder318.coefficient R d a i)
abbrev parameterUnit : Fˣ := IntegralReciprocalBase318.tUnit R a δ

/-- Literal reciprocal radicands, with each original d_i and a_i.
The source signed infinity root is y_i/t, not a root selected by its square. -/
lemma parameter_identity (i : Fin 4) : infinityParameter R a d i=
    finiteParameter R a d i*(↑(parameterUnit R a d)⁻¹:F)^2 := by
  rw [infinityParameter,IntegralInfinityReciprocalScalar318.baseMap_value]
  simp only [IntegralReciprocalBase318.reciprocalPolynomial,
    DVRNormalizedInfinityOrder318.coefficient,map_mul,map_sub,
    map_one,Polynomial.aeval_C,Polynomial.aeval_X]
  have hf : finiteParameter R a d i=algebraMap R F (d i)*
      ((parameterUnit R a d:F)-algebraMap R F (a i)) := by
    simp only [finiteParameter,DistinctContactIntegralDomain318.coefficient,map_mul,map_sub,
      IntegralReciprocalBase318.finite_C,IntegralReciprocalBase318.tUnit_coe]
    rfl
  rw [hf]
  have hu := Units.mul_inv (parameterUnit R a d)
  calc
    _ = algebraMap R F (d i)*(↑(parameterUnit R a d)⁻¹:F)*
      (((parameterUnit R a d:F)*(↑(parameterUnit R a d)⁻¹:F))-
        algebraMap R F (a i)*(↑(parameterUnit R a d)⁻¹:F)) := by rw [hu]
    _ = _ := by ring

/-- Entire source algebra equivalence, not merely the four equations. -/
@[expose] def sourceEquiv : FourRootOrder318.Order (infinityParameter R a d) ≃ₐ[F] OpenOrder R a d :=
  FourRootUnitScale318.four (finiteParameter R a d) (infinityParameter R a d)
    (parameterUnit R a d)⁻¹ (parameter_identity R a d)

lemma sourceEquiv_root (i : Fin 4) : sourceEquiv R a d
    (FourRootOrderSigns318.generator (infinityParameter R a d) i)=
      (↑(parameterUnit R a d)⁻¹:F) •
        FourRootOrderSigns318.generator (finiteParameter R a d) i :=
  FourRootUnitScale318.four_generator _ _ _ _ i
end IntegralInfinitySourceParameters318
