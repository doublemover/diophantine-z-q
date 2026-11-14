module
public import ActualTwoDescentInfinitySwappedCubic318
public section
noncomputable section
namespace ActualTwoDescentInfinityEisenstein318
open Polynomial ActualTwoDescentInfinitySwappedCubic318
variable {K : Type*} [Field K] [CharZero K]

/-- Eisenstein at the actual coefficient parameter v, for EVERY n.
The n=0 infinity chart is integral too; no whole-curve smoothness follows. -/
theorem actual_infinity_eisenstein (n : K) : Irreducible (swappedPolynomial n) := by
  let P : Ideal (Polynomial K) := Ideal.span {X}
  have hp : P.IsPrime := (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr
    (irreducible_X.prime)
  apply Polynomial.irreducible_of_eisenstein_criterion hp
  · rw [(actual_swapped_monic n).leadingCoeff]
    change (1 : Polynomial K) ∉ Ideal.span {X}
    simp [Ideal.mem_span_singleton,X_dvd_iff]
  · intro k hk
    rw [actual_swapped_degree] at hk
    have hk' : k<3 := by exact_mod_cast hk
    interval_cases k <;>
      simp [P,Ideal.mem_span_singleton,swappedPolynomial,Cubic.toPoly,X_dvd_iff]
  · rw [actual_swapped_degree]
    norm_num
  · intro h
    have h0 : (swappedPolynomial n).coeff 0= -(X : Polynomial K) := by
      simp [swappedPolynomial,Cubic.toPoly]
    rw [h0] at h
    change -(X : Polynomial K) ∈ (Ideal.span {X})^2 at h
    rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton] at h
    obtain ⟨g,hg⟩ := h
    have hc := congrArg (fun f : Polynomial K => f.coeff 1) hg
    norm_num [coeff_X_pow_mul] at hc
  · exact (actual_swapped_monic n).isPrimitive

instance swappedDomain (n : K) : IsDomain (SwappedChart n) :=
  AdjoinRoot.isDomain_of_prime (actual_infinity_eisenstein n).prime

lemma actual_swapped_u_nonzero (n : K) : swappedU n ≠ 0 := by
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt (actual_swapped_monic n) Polynomial.X_ne_zero
    (by rw [Polynomial.natDegree_X,actual_swapped_natDegree]; norm_num)

lemma actual_swapped_v_nonzero (n : K) : swappedV n ≠ 0 := by
  intro h
  apply Polynomial.X_ne_zero (R:=K)
  apply AdjoinRoot.of.injective_of_monic_of_degree_pos (actual_swapped_monic n)
    (by rw [actual_swapped_degree]; norm_num)
  simpa only [map_zero] using h

end ActualTwoDescentInfinityEisenstein318
