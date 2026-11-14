module
public import IntegralNormalizationTraceFunctional318
public import NormalTraceDualModule318
public section
noncomputable section
namespace IntegralNormalizationFiniteDual318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local notation "N" => IntegralFourRootNormalizationConductor318.normalOrder R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=F) N

include hd in
lemma base_injective : Function.Injective (algebraMap P F) :=
  IntegralInfinityArithmeticDomain318.away_injective P F
    (IntegralNormalizationConductorDenominator318.denominator R a d)
    (IntegralReciprocalBase318.finiteDenominator_ne_zero R a _
      (arithmeticDenominator_ne_zero R d hd))

/-- The full ACTUAL normalization trace codifferent is the finite dual
Hom_P(N,P), with its correct N action by multiplication precomposition.
No normal-order freeness or dualizing sheaf hypothesis is supplied. -/
@[expose] def equivalence : L ≃ₗ[N] FiniteDualModuleAction318.Dual P N where
  toFun := IntegralNormalizationTraceFunctional318.equivalence R a d hd
  invFun := (IntegralNormalizationTraceFunctional318.equivalence R a d hd).symm
  left_inv := (IntegralNormalizationTraceFunctional318.equivalence R a d hd).symm_apply_apply
  right_inv := (IntegralNormalizationTraceFunctional318.equivalence R a d hd).apply_symm_apply
  map_add' x y := by
    apply LinearMap.ext
    intro n
    apply base_injective R a d hd
    change algebraMap P F (IntegralNormalizationTraceFunctional318.equivalence R a d hd (x+y) n)=
      algebraMap P F (IntegralNormalizationTraceFunctional318.equivalence R a d hd x n +
        IntegralNormalizationTraceFunctional318.equivalence R a d hd y n)
    rw [map_add,IntegralNormalizationTraceFunctional318.trace_value,
      IntegralNormalizationTraceFunctional318.trace_value,
      IntegralNormalizationTraceFunctional318.trace_value]
    change Algebra.trace F B ((x.val+y.val)*n.val)=_
    rw [add_mul,map_add]
  map_smul' n z := by
    apply LinearMap.ext
    intro m
    change IntegralNormalizationTraceFunctional318.equivalence R a d hd (n • z) m=
      IntegralNormalizationTraceFunctional318.equivalence R a d hd z (n*m)
    apply base_injective R a d hd
    rw [IntegralNormalizationTraceFunctional318.trace_value,
      IntegralNormalizationTraceFunctional318.trace_value]
    congr 1
    change (n.val*z.val)*m.val=z.val*(n.val*m.val)
    ring

theorem trace_value (z : L) (n : N) :
    algebraMap P F (FiniteDualModuleAction318.evaluate P N (equivalence R a d hd z) n)=
      Algebra.trace F B (z.val*n.val) :=
  IntegralNormalizationTraceFunctional318.trace_value R a d hd z n
end IntegralNormalizationFiniteDual318
