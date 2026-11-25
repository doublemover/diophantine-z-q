module
public import OriginalNodeRingMaps318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section

namespace OriginalActualNodeDomain318

open Polynomial OriginalSplitNodeCoordinates318 OriginalNodeRingMaps318
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable (c : R) (hc : c ≠ 0)

include hc in
omit [UniqueFactorizationMonoid R] in
theorem primitive_equation : (equation c).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro a ha
  have hX : a ∣ (X : R[X]) := by
    have h := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp ha 1
    simpa [equation,coeff_C_mul,coeff_sub,coeff_X,coeff_C] using h
  have hC : a ∣ C c := by
    have h := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp ha 0
    have h' : a ∣ -(C c) := by simpa [equation,coeff_C_mul,coeff_sub,coeff_X,coeff_C] using h
    exact dvd_neg.mp h'
  apply (Polynomial.irreducible_X.isUnit_iff_not_associated_of_dvd hX).mpr
  intro h
  have hm : (X : R[X]) ∣ C c := dvd_trans h.dvd hC
  exact hc (by simpa using Polynomial.X_dvd_iff.mp hm)

omit [UniqueFactorizationMonoid R] in
theorem linear_degree : (equation c).degree = 1 := by
  have hd : (C (X:R[X]) * (X:R[X][X])).degree = 1 := by
    rw [Polynomial.degree_mul,Polynomial.degree_C Polynomial.X_ne_zero,Polynomial.degree_X,zero_add]
  have hn : (C (C c) : R[X][X]).degree < (C (X:R[X]) * X).degree := by
    rw [hd]
    exact Polynomial.degree_C_le.trans_lt (by decide : (0 : WithBot ℕ) < 1)
  rw [equation,Polynomial.degree_sub_eq_left_of_degree_lt hn,hd]

include hc in
theorem prime_equation : Prime (equation c) := by
  apply (UniqueFactorizationMonoid.irreducible_iff_prime).mp
  let K := FractionRing R[X]
  let f := algebraMap R[X] K
  apply (primitive_equation c hc).irreducible_of_irreducible_map_of_injective
    (IsFractionRing.injective _ K)
  apply Polynomial.irreducible_of_degree_eq_one
  rw [Polynomial.degree_map_eq_of_injective (IsFractionRing.injective _ K),linear_degree]

include hc in
theorem domain : IsDomain (Node c) :=
  AdjoinRoot.isDomain_of_prime (prime_equation c hc)

omit [UniqueFactorizationMonoid R] in
theorem scalar_injective : Function.Injective (algebraMap R (Node c)) := by
  have hn : (equation c).degree ≠ 0 := by rw [linear_degree]; decide
  exact (AdjoinRoot.of.injective_of_degree_ne_zero hn).comp Polynomial.C_injective

include hc in
omit [UniqueFactorizationMonoid R] in
theorem axes_nonzero : xAxis c ≠ 0 ∧ yAxis c ≠ 0 := by
  have hn := (scalar_injective c).ne hc
  rw [map_zero] at hn
  refine ⟨fun h => hn ?_,fun h => hn ?_⟩
  · rw [← node_relation,h,mul_zero]
  · rw [← node_relation,h,zero_mul]

end OriginalActualNodeDomain318

#print axioms OriginalActualNodeDomain318.prime_equation
#print axioms OriginalActualNodeDomain318.domain
#print axioms OriginalActualNodeDomain318.axes_nonzero
