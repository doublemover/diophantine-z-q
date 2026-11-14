module
public import LocalQuotientLengthSupport318
public import FourRootZeroSchemeSupport318
public section
noncomputable section
namespace FourRootCotangentWholeSupport318
open AlgebraicGeometry CategoryTheory
open FourRootGluedDerivativeIdeal318 FourRootDerivativeZeroIdeals318
open FourRootIntrinsicCanonicalFrames318
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
lemma finite_image_all (p : PrimeSpectrum (FourRootAffineCoordinateRing318.Ring b)) :
    FourRootGluedScheme318.finiteChart b p ∈ Set.range (into b) ↔ finiteIdeal b ≤ p.asIdeal := by
  rw [FourRootZeroSchemeSupport318.image_square (finiteChart b) (FourRootGluedScheme318.finiteChart b)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (finiteIdeal b)))) (into b)
    (FourRootGluedScheme318.finiteChart b).isOpenEmbedding.injective
    (fun a => congrArg (fun f : finiteZero b ⟶ FourRootGluedScheme318.scheme b => f a)
      (finiteChart_into b))
    (fun z hz => by
      change z ∈ (finiteChart b).opensRange
      rw [←FourRootDerivativeIdealClosed318.finite_preimage]
      exact hz)]
  exact LocalQuotientLengthSupport318.quotient_image _ _
lemma infinity_image_all (p : PrimeSpectrum (FourRootInfinityCoordinateRing318.Ring b)) :
    FourRootGluedScheme318.infinityChart b p ∈ Set.range (into b) ↔ infinityIdeal b ≤ p.asIdeal := by
  rw [FourRootZeroSchemeSupport318.image_square (infinityChart b) (FourRootGluedScheme318.infinityChart b)
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (infinityIdeal b)))) (into b)
    (FourRootGluedScheme318.infinityChart b).isOpenEmbedding.injective
    (fun a => congrArg (fun f : infinityZero b ⟶ FourRootGluedScheme318.scheme b => f a)
      (infinityChart_into b))
    (fun z hz => by
      change z ∈ (infinityChart b).opensRange
      rw [←FourRootDerivativeIdealClosed318.infinity_preimage]
      exact hz)]
  exact LocalQuotientLengthSupport318.quotient_image _ _
lemma finite_zero (p : PrimeSpectrum (FourRootAffineCoordinateRing318.Ring b))
    (hp : FourRootGluedScheme318.finiteChart b p ∉ Set.range (into b)) :
    FourRootCotangentStalkQuotient318.length b (FourRootGluedScheme318.finiteChart b p) = 0 := by
  rw [FourRootActualSheafLengths318.finite_prime_length b hb]
  exact LocalQuotientLengthSupport318.length_zero _ p (fun h => hp ((finite_image_all b p).mpr h))
lemma infinity_zero (p : PrimeSpectrum (FourRootInfinityCoordinateRing318.Ring b))
    (hd : FourRootActualInfinityKaehler318.denominator b hb ∉ p.asIdeal)
    (hp : FourRootGluedScheme318.infinityChart b p ∉ Set.range (into b)) :
    FourRootCotangentStalkQuotient318.length b (FourRootGluedScheme318.infinityChart b p) = 0 := by
  rw [FourRootActualSheafLengths318.infinity_prime_length b hb p hd]
  exact LocalQuotientLengthSupport318.length_zero _ p (fun h => hp ((infinity_image_all b p).mpr h))
/-- At EVERY prime of the original whole scheme outside the actual
closed derivative-zero subscheme, the canonical cotangent stalk has
length zero. Nonclosed and generic points are included explicitly. -/
theorem outside_length_zero (x : FourRootGluedScheme318.scheme b)
    (hx : x ∉ Set.range (into b)) : FourRootCotangentStalkQuotient318.length b x = 0 := by
  rcases FourRootWholeCanonicalCover318.frames_cover b hb x with ⟨i,q,rfl⟩ | ⟨q,rfl⟩
  · exact finite_zero b hb
      (q.comap (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i))) hx
  · let p := q.comap (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb))
    have hp : FourRootActualInfinityKaehler318.denominator b hb ∉ p.asIdeal := by
      have h : p ∈ Set.range (PrimeSpectrum.comap
          (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb))) := ⟨q,rfl⟩
      rwa [PrimeSpectrum.localization_away_comap_range (InfinityRing b hb)
        (FourRootActualInfinityKaehler318.denominator b hb)] at h
    exact infinity_zero b hb p hp hx
end FourRootCotangentWholeSupport318
