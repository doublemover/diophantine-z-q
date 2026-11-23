module
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

public section
noncomputable section

namespace SelectedJIntegralScaledTraceDual318

open Algebra Module
open scoped nonZeroDivisors Pointwise

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A B : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B]
  [IsIntegralClosure B A (FractionRing B)]
  [FiniteDimensional (FractionRing A) (FractionRing B)]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

local notation "K" => FractionRing A
local notation "L" => FractionRing B

/-- The exact integral basis, extended along the actual localization map. -/
def genericBasis {ι : Type*} (b : Basis ι A B) : Basis ι K L :=
  let : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization_of_isSeparable A K L B
  b.localizationLocalization K A⁰ L

private theorem repr_algebraMap {ι : Type*} (b : Basis ι A B) (x : B) (i : ι) :
    (genericBasis A B b).repr (algebraMap B L x) i = algebraMap A K (b.repr x i) := by
  unfold genericBasis
  exact b.localizationLocalization_repr_algebraMap K A⁰ L x i

/-- Scale the actual trace-dual basis into the same integral closure, using
membership in the Dedekind different rather than a monogenic hypothesis. -/
theorem exists_scaled_traceDual {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι A B) (a : B) (ha : a ∈ differentIdeal A B) :
    ∃ c : ι → B, ∀ i, algebraMap B L (c i) =
      algebraMap B L a * (genericBasis A B b).traceDual i := by
  let bK := genericBasis A B b
  have liftOne (i : ι) : ∃ c : B,
      algebraMap B L c = algebraMap B L a * bK.traceDual i := by
    have hdual : bK.traceDual i ∈ Submodule.traceDual A K (1 : Submodule B L) := by
      rw [Submodule.mem_traceDual]
      intro y hy
      obtain ⟨x, rfl⟩ := Submodule.mem_one.mp hy
      refine ⟨b.repr x i, ?_⟩
      have hx := (bK.traceDual).traceDual_repr_apply (algebraMap B L x) i
      rw [Module.Basis.traceDual_traceDual] at hx
      calc
        algebraMap A K (b.repr x i) = bK.repr (algebraMap B L x) i :=
          (repr_algebraMap A B b x i).symm
        _ = traceForm K L (algebraMap B L x) (bK.traceDual i) := hx
        _ = traceForm K L (bK.traceDual i) (algebraMap B L x) := by
          rw [traceForm_apply, traceForm_apply, mul_comm]
    have ha' : algebraMap B L a ∈
        (1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L) := ha
    exact Submodule.mem_one.mp ((Submodule.mem_div_iff_forall_mul_mem.mp ha') _ hdual)
  exact ⟨fun i => (liftOne i).choose, fun i => (liftOne i).choose_spec⟩

end SelectedJIntegralScaledTraceDual318

#print axioms SelectedJIntegralScaledTraceDual318.exists_scaled_traceDual
