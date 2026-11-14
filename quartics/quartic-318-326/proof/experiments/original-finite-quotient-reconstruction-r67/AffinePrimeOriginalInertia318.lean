module
public import AffinePrimeCenter318
public import PrimeLocalizationInertia318
public section
noncomputable section
namespace AffinePrimeOriginalInertia318
variable {B L : Type*} [CommRing B] [IsDomain B] [Field L]
  [Algebra B L] [IsFractionRing B L]
  (P : Ideal B) [P.IsPrime] (a : B ≃+* B) (hP : P = P.comap a)
  (σ : L ≃+* L)

/-- Restriction to the actual local ring is CONSTRUCTED from the original
prime-preserving affine action and its unchanged generic square. -/
lemma generic_square
    (hσ : ∀ b : B, σ (algebraMap B L b) = algebraMap B L (a b))
    (x : Localization.AtPrime P) :
    σ (PrimeLocalOriginalField318.embedding B L P x) =
      PrimeLocalOriginalField318.embedding B L P
        (PrimeLocalizationInertia318.lift P (Localization.AtPrime P) a hP x) := by
  have hh : σ.toRingHom.comp (PrimeLocalOriginalField318.embedding B L P) =
      (PrimeLocalOriginalField318.embedding B L P).comp
        (PrimeLocalizationInertia318.lift P (Localization.AtPrime P) a hP).toRingHom := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext b
    change σ (PrimeLocalOriginalField318.embedding B L P
      (algebraMap B (Localization.AtPrime P) b)) =
      PrimeLocalOriginalField318.embedding B L P
        (PrimeLocalizationInertia318.lift P (Localization.AtPrime P) a hP
          (algebraMap B (Localization.AtPrime P) b))
    rw [PrimeLocalOriginalField318.embedding_integral,
      PrimeLocalizationInertia318.lift_algebraMap,
      PrimeLocalOriginalField318.embedding_integral, hσ b]
  exact RingHom.congr_fun hh x

/-- Inertia on the full residue field follows from the actual affine
modulo-prime action; it is not assumed on arbitrary local fractions. -/
lemma residue_identity (h : ∀ b : B, a b - b ∈ P)
    (x : Localization.AtPrime P) :
    IsLocalRing.residue (Localization.AtPrime P)
      (PrimeLocalizationInertia318.lift P (Localization.AtPrime P) a hP x) =
    IsLocalRing.residue (Localization.AtPrime P) x :=
  (PrimeLocalizationInertia318.residue_trivial_iff P (Localization.AtPrime P) a hP).mpr h x
end AffinePrimeOriginalInertia318
