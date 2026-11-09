module
public import InertiaTangentUniformizer318
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public section
noncomputable section
namespace TameInvolutionUniformizer318
open IsLocalRing IsDiscreteValuationRing
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero (ResidueField R)]

/-- If the original local inertia acts trivially on the tangent line, it
cannot have a nonzero anti-invariant element. This uses the genuine leading
coefficient in the full residue field, not a formal-series expansion. -/
lemma no_anti_if_tangent_one (τ : R ≃+* R)
    (hres : ∀ x : R, residue R (τ x) = residue R x)
    (p : R) (hp : Irreducible p) (u : Rˣ) (hpu : τ p = p * u)
    (hu : residue R (u : R) = 1) (y : R) (hy : y ≠ 0) (hτy : τ y = -y) : False := by
  obtain ⟨n, v, hv⟩ := eq_unit_mul_pow_irreducible hy hp
  have he : τ (v : R) * (u : R) ^ n = -(v : R) := by
    apply mul_right_cancel₀ (pow_ne_zero n hp.ne_zero)
    calc
      _ = τ ((v : R) * p ^ n) := by
        rw [map_mul, map_pow, hpu, mul_pow] <;> ring
      _ = -((v : R) * p ^ n) := by rw [← hv, hτy]
      _ = _ := by ring
  have hr : residue R (v : R) = -residue R (v : R) := by
    simpa only [map_mul, map_pow, map_neg, hres, hu, one_pow, mul_one] using
      congrArg (residue R) he
  have hz : (2 : ResidueField R) * residue R (v : R) = 0 := by
    linear_combination hr
  exact (mul_ne_zero (by norm_num) ((residue_ne_zero_iff_isUnit _).mpr v.isUnit)) hz

/-- Nontrivial order2 inertia in residue characteristic0 has tangent sign-1.
The original uniformizer need not have been chosen as an eigenvector. -/
theorem tangent_negative (τ : R ≃+* R) (hτ : ∀ x, τ (τ x) = x)
    (hres : ∀ x : R, residue R (τ x) = residue R x)
    (hmoves : ∃ x : R, τ x ≠ x) (p : R) (hp : Irreducible p) :
    p ^ 2 ∣ τ p + p := by
  obtain ⟨u, hu⟩ := associated_of_irreducible R hp ((MulEquiv.irreducible_iff τ).mpr hp)
  have hpu : τ p = p * u := hu.symm
  have hs : (u : R) * τ (u : R) = 1 := by
    apply mul_left_cancel₀ hp.ne_zero
    calc
      _ = τ (τ p) := by rw [hpu, map_mul, hpu] <;> ring
      _ = p := hτ p
      _ = _ := (mul_one p).symm
  have hsq : (residue R (u : R)) ^ 2 = 1 := by
    simpa only [map_mul, map_one, hres, pow_two] using congrArg (residue R) hs
  have hne : residue R (u : R) ≠ 1 := by
    intro h
    obtain ⟨x, hx⟩ := hmoves
    have hdiff : x - τ x ≠ 0 := sub_ne_zero.mpr hx.symm
    have hanti : τ (x - τ x) = -(x - τ x) := by
      rw [map_sub, hτ] <;> ring
    exact no_anti_if_tangent_one τ hres p hp u hpu h (x - τ x) hdiff hanti
  have hneg : residue R (u : R) = -1 := by
    have hz : (residue R (u : R) - 1) * (residue R (u : R) + 1) = 0 := by
      linear_combination hsq
    exact eq_neg_of_add_eq_zero ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne))
  have hmem : (u : R) + 1 ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simp only [map_add, map_one, hneg, neg_add_cancel]
  rw [(irreducible_iff_uniformizer p).mp hp, Ideal.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, ?_⟩
  rw [hpu]
  calc
    p * (u : R) + p = p * ((u : R) + 1) := by ring
    _ = p * (p * a) := by rw [ha]
    _ = p ^ 2 * a := by ring

/-- The original tame involution produces the required eigen-uniformizer;
no tangent-character or eigen-uniformizer input remains. -/
theorem exists_anti_uniformizer (τ : R ≃+* R) (hτ : ∀ x, τ (τ x) = x)
    (hres : ∀ x : R, residue R (τ x) = residue R x)
    (hmoves : ∃ x : R, τ x ≠ x) :
    ∃ π : R, Irreducible π ∧ τ π = -π := by
  obtain ⟨p, hp⟩ := exists_irreducible R
  exact ⟨InertiaTangentUniformizer318.anti τ p,
    InertiaTangentUniformizer318.anti_uniformizer τ hτ p hp
      (tangent_negative τ hτ hres hmoves p hp)⟩
end TameInvolutionUniformizer318
