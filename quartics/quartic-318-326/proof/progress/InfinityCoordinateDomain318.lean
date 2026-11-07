module
public import AffineCoordinateDomain318
public import WeierstrassOverlap318
public import Mathlib.Algebra.MvPolynomial.Division
public section
noncomputable section
namespace InfinityCoordinateDomain318
open MvPolynomial WeierstrassOverlap318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R] [IsDomain R]

lemma affine_y_ne_zero (A B:R) : ShortAffineJacobian318.y A B ≠ 0 := by
  intro h
  have hn := (WeierstrassCurve.Affine.CoordinateRing.basis (AffineCoordinateDomain318.model A B)).ne_zero (1:Fin 2)
  apply hn
  rw [WeierstrassCurve.Affine.CoordinateRing.basis_one]
  change AffineCoordinateDomain318.y A B=0
  rw [←AffineCoordinateDomain318.forward_y,h,map_zero]

theorem affine_overlap_domain (A B:R) : IsDomain (AffineOverlap A B) := by
  have := AffineCoordinateDomain318.affine_domain A B
  exact IsLocalization.Away.isDomain (AffineOverlap A B) (affine_y_ne_zero A B)
theorem infinity_overlap_domain (A B:R) : IsDomain (InfinityOverlap A B) := by
  have := affine_overlap_domain A B
  exact (overlapEquiv A B).injective.isDomain

lemma equation_not_z_dvd (A B:R) : ¬ X (1:Fin 2) ∣ InfinityChart318.equation A B := by
  rintro ⟨q,hq⟩
  have h := congrArg (aeval ![Polynomial.X,0] : MvPolynomial (Fin 2) R →ₐ[R] Polynomial R) hq
  simp [InfinityChart318.equation] at h

lemma defining_ideal (A B:R) : Ideal.span (Set.range (InfinityChart318.equations A B))=
    Ideal.span ({InfinityChart318.equation A B}:Set (MvPolynomial (Fin 2) R)) := by
  congr 1
  ext q
  constructor
  · rintro ⟨i,rfl⟩; rfl
  · intro h; exact ⟨(),h.symm⟩

/-- The literal infinity denominator is a non-zero-divisor in the original quotient. -/
theorem z_regular (A B:R) : InfinityChart318.z A B ∈ nonZeroDivisors (Infinity A B) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro t ht
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective t
  change (Ideal.Quotient.mk _) (X 1)*(Ideal.Quotient.mk _) q=0 at ht
  rw [←map_mul,Ideal.Quotient.eq_zero_iff_mem,defining_ideal,Ideal.mem_span_singleton] at ht
  have hq : InfinityChart318.equation A B ∣ q := by
    rcases MvPolynomial.dvd_X_mul_iff.mp ht with h | ⟨h,_⟩
    · exact h
    · exact (equation_not_z_dvd A B h).elim
  rw [Ideal.Quotient.eq_zero_iff_mem,defining_ideal,Ideal.mem_span_singleton]
  exact hq

theorem localization_injective (A B:R) : Function.Injective
    (algebraMap (Infinity A B) (InfinityOverlap A B)) := by
  apply IsLocalization.injective (M := Submonoid.powers (InfinityChart318.z A B))
  rintro q ⟨n,rfl⟩
  exact (nonZeroDivisors (Infinity A B)).pow_mem (z_regular A B) n

/-- The entire actual infinity coordinate ring is a domain, without a smoothness assumption. -/
theorem infinity_domain (A B:R) : IsDomain (Infinity A B) := by
  have := infinity_overlap_domain A B
  exact (localization_injective A B).isDomain

end InfinityCoordinateDomain318
