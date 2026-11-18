module
public import IntegralInfinityTraceFunctional318
public import NormalTraceDualModule318
public section
noncomputable section
namespace IntegralInfinityFiniteDual318
open Polynomial IntegralDistinctContactOpen318
variable (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
  [IsNoetherianRing R] [IsIntegrallyClosed R[X]] (a d : Fin 4 → R)
  [IsDomain (OpenOrder R a d)] (hd : ∀ i,d i ≠ 0)
local notation "P" => Polynomial R
local notation "F" => Base R a d
local notation "B" => OpenOrder R a d
local instance : Algebra P F := IntegralInfinityReciprocalScalar318.baseAlgebra R a d
local instance : Algebra P B := IntegralInfinityReciprocalScalar318.sourceAlgebra R a d
local instance : IsScalarTower P F B := IntegralInfinityReciprocalScalar318.tower R a d
local notation "N" => IntegralInfinityNormalConductor318.normalOrder R a d
local notation "L" => NormalTraceDualModule318.lattice (F:=F) N

include hd in
lemma base_injective : Function.Injective (algebraMap P F) :=
  IntegralInfinityRawEmbedding318.base_injective R a d hd

/-- The full ACTUAL reciprocal normalization trace codifferent is the finite dual
Hom_P(N,P), with its correct N action by multiplication precomposition.
No normal-order freeness or dualizing sheaf hypothesis is supplied. -/
@[expose] def equivalence : L ≃ₗ[N] FiniteDualModuleAction318.Dual P N where
  toFun := IntegralInfinityTraceFunctional318.equivalence R a d hd
  invFun := (IntegralInfinityTraceFunctional318.equivalence R a d hd).symm
  left_inv := (IntegralInfinityTraceFunctional318.equivalence R a d hd).symm_apply_apply
  right_inv := (IntegralInfinityTraceFunctional318.equivalence R a d hd).apply_symm_apply
  map_add' x y := by
    apply LinearMap.ext
    intro n
    apply base_injective R a d hd
    change algebraMap P F (IntegralInfinityTraceFunctional318.equivalence R a d hd (x+y) n)=
      algebraMap P F (IntegralInfinityTraceFunctional318.equivalence R a d hd x n +
        IntegralInfinityTraceFunctional318.equivalence R a d hd y n)
    rw [map_add,IntegralInfinityTraceFunctional318.trace_value,
      IntegralInfinityTraceFunctional318.trace_value,
      IntegralInfinityTraceFunctional318.trace_value]
    change Algebra.trace F B ((x.val+y.val)*n.val)=_
    rw [add_mul,map_add]
  map_smul' n z := by
    apply LinearMap.ext
    intro m
    change IntegralInfinityTraceFunctional318.equivalence R a d hd (n • z) m=
      IntegralInfinityTraceFunctional318.equivalence R a d hd z (n*m)
    apply base_injective R a d hd
    rw [IntegralInfinityTraceFunctional318.trace_value,
      IntegralInfinityTraceFunctional318.trace_value]
    congr 1
    change (n.val*z.val)*m.val=z.val*(n.val*m.val)
    ring

theorem trace_value (z : L) (n : N) :
    algebraMap P F (FiniteDualModuleAction318.evaluate P N (equivalence R a d hd z) n)=
      Algebra.trace F B (z.val*n.val) :=
  IntegralInfinityTraceFunctional318.trace_value R a d hd z n
end IntegralInfinityFiniteDual318
