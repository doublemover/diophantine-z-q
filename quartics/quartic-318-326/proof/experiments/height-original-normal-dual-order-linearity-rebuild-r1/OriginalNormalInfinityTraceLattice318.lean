module
public import IntegralInfinityFiniteDual318
public section
noncomputable section
namespace OriginalNormalInfinityTraceLattice318
open AlgebraicGeometry CategoryTheory NumberField Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "a" => contacts c t w
local notation "d" => D.coefficients
local notation "F" => IntegralDistinctContactOpen318.Base R a d
local notation "B" => SourceOpenRing c t w D
local instance : Algebra P F := IntegralInfinityReciprocalScalar318.baseAlgebra R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : IsScalarTower P F B := IntegralInfinityReciprocalScalar318.tower R a d
local notation "N" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "C" => OriginalNormalInfinityOrder318.Order c t w D
abbrev Lattice := NormalTraceDualModule318.lattice (F:=F) N
local notation "L" => Lattice c t w D

/-- Exact SAME whole reciprocal normal-order carrier and scalar:
this is the order used by the actual infinity chart, not a new model. -/
lemma order_identity : N=C := rfl

@[expose] def traceSheaf : (Spec (CommRingCat.of C)).Modules :=
  tilde (R:=CommRingCat.of C) (ModuleCat.of C L)

/-- The ENTIRE actual infinity finite dual is now identified with the
literal trace lattice in the SAME original source, with its correct order
action. This closes the previous affine infinity trace-identity boundary. -/
@[expose] def traceSheafIso : traceSheaf c t w D ≅
    OriginalNormalInfinityDuality318.dualSheaf c t w D := by
  letI : IsDomain B := IntegralDistinctContactOpen318.open_domain R a d (K c t)
    (IsFractionRing.injective R (K c t)) (contacts_injective c t w)
    (coefficients_ne_zero c t w D)
  have hα : (OriginalNormalInfinityOrder318.polynomialScalar c t w D).toAlgebra=
      (inferInstance : Algebra P C) := toAlgebra_algebraMap (R:=P) (S:=C)
  unfold OriginalNormalInfinityDuality318.dualSheaf
  rw [hα]
  exact (tilde.functor (CommRingCat.of C)).mapIso
    (IntegralInfinityFiniteDual318.equivalence R a d (coefficients_ne_zero c t w D)).toModuleIso

/-- Actual source differential realization uses dS for the literal
inverse coordinate, rather than reusing the finite dT generator. -/
@[expose] def form (z : L) : KaehlerDifferential R B :=
  (IntegralNormalReciprocalForms318.reciprocalFrame R a d).symm z.val

lemma reciprocal_coefficient (z : L) :
    IntegralNormalReciprocalForms318.reciprocalFrame R a d (form c t w D z)=z.val :=
  (IntegralNormalReciprocalForms318.reciprocalFrame R a d).apply_symm_apply z.val

@[expose] def value (z : L) : K c t := M.fieldPoint z.val

/-- The true raw infinity different corrects the WHOLE normal trace
lattice into the actual conductor, hence into the integral infinity order. -/
theorem corrected_value_bound (ht : w (t:K c t)⁻¹ ≤ 1) (z : L) :
    w (M.fieldPoint (IntegralInfinityNormalConductor318.different R a d)*value c t w D M z) ≤ 1 := by
  have hz : z.val ∈ IntegralInfinityNormalConductor318.codifferent R a d := z.property
  have hc := (IntegralInfinityNormalConductor318.mem_codifferent_iff R a d z.val).mp hz
  have hn := IntegralInfinityNormalConductor318.conductor_le_normal R a d hc
  have hb := OriginalNormalInfinityIntegralPoint318.normal_value_bound c t w D M ht
    ⟨IntegralInfinityNormalConductor318.different R a d*z.val,hn⟩
  simpa only [value,map_mul] using hb
end OriginalNormalInfinityTraceLattice318
