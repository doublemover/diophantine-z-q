module
public import FourRootCotangentStalkQuotient318
public import AffineStalkLocalizationLength318
public import FourRootWholeCanonicalCover318
public import FourRootFiniteZeroLocalLength318
public import FourRootInfinityZeroLocalLength318
public import FourRootCompletedSchemePoints318
public section
noncomputable section
namespace FourRootActualSheafLengths318
open AlgebraicGeometry CategoryTheory
open FourRootIntrinsicCanonicalFrames318 FourRootNormalizedPointCharts318
open FourRootActualResidueInertia318
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
/-- For every prime of the ORIGINAL whole finite affine ring, compare
the actual global sheaf stalk with the exact localized whole zero ideal.
The principal canonical chart is produced by the proved all-prime cover. -/
theorem finite_prime_length (p : PrimeSpectrum (FourRootAffineCoordinateRing318.Ring b)) :
    FourRootCotangentStalkQuotient318.length b (FourRootGluedScheme318.finiteChart b p) =
      Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ (FourRootDerivativeZeroIdeals318.finiteIdeal b).map
          (algebraMap (FourRootAffineCoordinateRing318.Ring b) _)) := by
  obtain ⟨i,hi⟩ := FourRootActualFrameDenominatorCover318.finite_cover b hb p
  have hm : p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i))) := by
    rw [PrimeSpectrum.localization_away_comap_range (FiniteRing b i)
      (FourRootActualFiniteBranchChart318.denominator b i)]
    exact hi
  obtain ⟨q,hq⟩ := hm
  have hpoint : finiteEmbedding b i q = FourRootGluedScheme318.finiteChart b p :=
    congrArg (FourRootGluedScheme318.finiteChart b) hq
  rw [← hpoint,FourRootCotangentStalkQuotient318.finite_length b hb i q,
    AffineStalkLocalizationLength318.length_eq]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i)))) :=
    IsOpenImmersion.of_isLocalization (FourRootActualFiniteBranchChart318.denominator b i)
  change Module.length (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime q.asIdeal ⧸
      ((FourRootDerivativeZeroIdeals318.finiteIdeal b).map
        (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i))).map
          (algebraMap (FiniteRing b i) _)) = _
  rw [LocalIdealLengthTransport318.length_eq,hq]

/-- The original infinity point lies in the canonical infinity open by
its actual nonvanishing denominator, not by a guessed local parameter. -/
theorem infinity_prime_length (p : PrimeSpectrum (FourRootInfinityCoordinateRing318.Ring b))
    (hp : FourRootActualInfinityKaehler318.denominator b hb ∉ p.asIdeal) :
    FourRootCotangentStalkQuotient318.length b (FourRootGluedScheme318.infinityChart b p) =
      Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ (FourRootDerivativeZeroIdeals318.infinityIdeal b).map
          (algebraMap (FourRootInfinityCoordinateRing318.Ring b) _)) := by
  have hm : p ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb))) := by
    rw [PrimeSpectrum.localization_away_comap_range (InfinityRing b hb)
      (FourRootActualInfinityKaehler318.denominator b hb)]
    exact hp
  obtain ⟨q,hq⟩ := hm
  have hpoint : infinityEmbedding b hb q = FourRootGluedScheme318.infinityChart b p :=
    congrArg (FourRootGluedScheme318.infinityChart b) hq
  rw [← hpoint,FourRootCotangentStalkQuotient318.infinity_length b hb q,
    AffineStalkLocalizationLength318.length_eq]
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb)))) :=
    IsOpenImmersion.of_isLocalization (FourRootActualInfinityKaehler318.denominator b hb)
  change Module.length (Localization.AtPrime q.asIdeal)
    (Localization.AtPrime q.asIdeal ⧸
      ((FourRootDerivativeZeroIdeals318.infinityIdeal b).map
        (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb))).map
          (algebraMap (InfinityRing b hb) _)) = _
  rw [LocalIdealLengthTransport318.length_eq,hq]

lemma complex_point {R : Type} [CommRing R] (f : R →+* ℂ) :
    (Spec.map (CommRingCat.ofHom f)) default =
      (⟨RingHom.ker f,RingHom.ker_isPrime f⟩ : PrimeSpectrum R) := by
  have hd : (default : PrimeSpectrum ℂ).asIdeal = ⊥ :=
    congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (default : PrimeSpectrum ℂ) ⟨⊥,by infer_instance⟩)
  apply PrimeSpectrum.ext
  change Ideal.comap f (default : PrimeSpectrum ℂ).asIdeal = RingHom.ker f
  rw [hd]
  rfl
/-- The prime used above is the point of the SAME original complex-valued
Scheme morphism, not a newly chosen closed point with matching coordinates. -/
lemma finite_point (p : FinitePoints b) :
    (FourRootCompletedSchemePoints318.finitePoint b p).val default =
      FourRootGluedScheme318.finiteChart b ⟨finitePrime b p,finite_prime b p⟩ := by
  change FourRootGluedScheme318.finiteChart b
    ((Spec.map (CommRingCat.ofHom (finiteEvaluation b p).toRingHom)) default) = _
  rw [complex_point]
lemma infinity_point (p : InfinityPoints b) :
    (FourRootCompletedSchemePoints318.infinityPoint b p).val default =
      FourRootGluedScheme318.infinityChart b ⟨infinityPrime b p,infinity_prime b p⟩ := by
  change FourRootGluedScheme318.infinityChart b
    ((Spec.map (CommRingCat.ofHom (infinityEvaluation b p).toRingHom)) default) = _
  rw [complex_point]
theorem finite_length (p : FinitePoints b) :
    FourRootCotangentStalkQuotient318.length b
      ((FourRootCompletedSchemePoints318.finitePoint b p).val default) =
        FourRootFiniteZeroLocalLength318.localLength b p := by
  rw [finite_point]
  exact finite_prime_length b hb ⟨finitePrime b p,finite_prime b p⟩
theorem infinity_length (p : InfinityPoints b) (hp : p.val.1 = 0) :
    FourRootCotangentStalkQuotient318.length b
      ((FourRootCompletedSchemePoints318.infinityPoint b p).val default) =
        FourRootInfinityZeroLocalLength318.localLength b p := by
  rw [infinity_point]
  apply infinity_prime_length b hb ⟨infinityPrime b p,infinity_prime b p⟩
  exact FourRootActualKaehlerNeighborhoods318.infinity_neighborhood b hb p hp
end FourRootActualSheafLengths318
