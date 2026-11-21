module
public import Mathlib.RingTheory.Frobenius
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public section
namespace ActualGaussianNativeFrobenius318

variable {S : Type*} [CommRing S] [Algebra ℤ S]

/-- For a prime over the actual rational ideal (p), Mathlib's arithmetic
Frobenius exponent is exactly p. This uses the literal rational ideal
quotient, not a degree-one assumption on the Gaussian contraction. -/
theorem rational_exponent (p : ℕ) (hp : p.Prime) (Q : Ideal S)
    (hQ : Q.under ℤ = Ideal.span ({(p:ℤ)} : Set ℤ)) :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [hQ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card]

/-- Contract the native arithmetic Frobenius congruence along the SAME
Gaussian inclusion. The sole split input is that the automorphism
fixes this embedded Gaussian subring, as it does on the A_M subgroup.
The conclusion is the exact hFix which the old arithmetic ideal
bridge converts to a degree-one prime and a norm-p generator. -/
theorem gaussian_quotient_power (p : ℕ) (hp : p.Prime) (Q : Ideal S)
    (hQ : Q.under ℤ = Ideal.span ({(p:ℤ)} : Set ℤ))
    (ι : GaussianInt →+* S) (φ : S →ₐ[ℤ] S)
    (hF : φ.IsArithFrobAt Q) (hFix : ∀ z, φ (ι z) = ι z) :
    ∀ z : GaussianInt,
      (Ideal.Quotient.mk (Q.comap ι) z)^p = Ideal.Quotient.mk (Q.comap ι) z := by
  intro z
  have h : φ (ι z) - (ι z) ^ Nat.card (ℤ ⧸ Q.under ℤ) ∈ Q := hF (ι z)
  rw [hFix z,rational_exponent p hp Q hQ,←map_pow,←map_sub] at h
  have hm : z-z^p ∈ Q.comap ι := h
  have he : Ideal.Quotient.mk (Q.comap ι) z = Ideal.Quotient.mk (Q.comap ι) (z^p) :=
    (Ideal.Quotient.eq (I:=Q.comap ι)).mpr hm
  simpa only [map_pow] using he.symm

theorem rational_prime_in_contraction (p : ℕ) (Q : Ideal S)
    (hQ : Q.under ℤ = Ideal.span ({(p:ℤ)} : Set ℤ)) (ι : GaussianInt →+* S) :
    (p:GaussianInt) ∈ Q.comap ι := by
  have h : (p:ℤ) ∈ Q.under ℤ := by
    rw [hQ]
    exact Ideal.mem_span_singleton_self (p:ℤ)
  change algebraMap ℤ S (p:ℤ) ∈ Q at h
  change ι (p:GaussianInt) ∈ Q
  simpa only [map_natCast] using h

/-- Directly invoke the pinned Mathlib chosen arithmetic Frobenius. The
number-field/Gaussian class proof must still identify its restriction;
the p-th-power congruence no longer has to be postulated externally. -/
theorem chosen_frob_quotient_power {G : Type*} [Group G] [Finite G]
    [MulSemiringAction G S] [SMulCommClass G ℤ S] [Algebra.IsInvariant ℤ S G]
    (p : ℕ) (hp : p.Prime) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (hQ : Q.under ℤ = Ideal.span ({(p:ℤ)} : Set ℤ)) (ι : GaussianInt →+* S)
    (hFix : ∀ z, arithFrobAt ℤ G Q • ι z = ι z) :
    ∀ z : GaussianInt,
      (Ideal.Quotient.mk (Q.comap ι) z)^p = Ideal.Quotient.mk (Q.comap ι) z :=
  gaussian_quotient_power p hp Q hQ ι
    (MulSemiringAction.toAlgHom ℤ S (arithFrobAt ℤ G Q))
    (IsArithFrobAt.arithFrobAt ℤ G Q) hFix

end ActualGaussianNativeFrobenius318
