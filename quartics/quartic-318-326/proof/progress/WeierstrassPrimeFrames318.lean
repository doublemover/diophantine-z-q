module
public import LocalizedKaehlerFrame318
public import WeierstrassKaehler318
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public section
noncomputable section
namespace WeierstrassPrimeFrames318
open KaehlerDifferential WeierstrassKaehler318 LocalizedKaehlerFrame318
set_option maxHeartbeats 200000
variable {R : Type*} [CommRing R]

/-- Actual prime-localization frame on either Weierstrass Jacobian chart. -/
@[expose] def affinePrimeFrame (A B : R) (i : Fin 2)
    (p : Ideal (AffineChart A B i)) [p.IsPrime] :
    KaehlerDifferential R (Localization.AtPrime p) ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  localFrame p.primeCompl (affineFrame A B i)

/-- Actual prime-localization frame on the infinity Jacobian chart. -/
@[expose] def infinityPrimeFrame (A B : R)
    (p : Ideal (InfinityChart318.SmoothRing A B)) [p.IsPrime] :
    KaehlerDifferential R (Localization.AtPrime p) ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
  localFrame p.primeCompl (infinityFrame A B)

theorem affinePrimeFrame_dx (A B : R) (p : Ideal (AffineChart A B 1)) [p.IsPrime] :
    affinePrimeFrame A B 1 p (D R (Localization.AtPrime p)
      (algebraMap (AffineChart A B 1) (Localization.AtPrime p)
        (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 1)
          (ShortAffineJacobian318.x A B)))) = 1 :=
  localFrame_normalized p.primeCompl (affineFrame A B 1) _ (affineFrame_dx A B)

theorem affinePrimeFrame_dy (A B : R) (p : Ideal (AffineChart A B 0)) [p.IsPrime] :
    affinePrimeFrame A B 0 p (D R (Localization.AtPrime p)
      (algebraMap (AffineChart A B 0) (Localization.AtPrime p)
        (algebraMap (ShortAffineJacobian318.Ring A B) (AffineChart A B 0)
          (ShortAffineJacobian318.y A B)))) = 1 :=
  localFrame_normalized p.primeCompl (affineFrame A B 0) _ (affineFrame_dy A B)

theorem infinityPrimeFrame_dx (A B : R) (p : Ideal (InfinityChart318.SmoothRing A B)) [p.IsPrime] :
    infinityPrimeFrame A B p (D R (Localization.AtPrime p)
      (algebraMap (InfinityChart318.SmoothRing A B) (Localization.AtPrime p)
        (algebraMap (InfinityChart318.Ring A B) (InfinityChart318.SmoothRing A B)
          (InfinityChart318.x A B)))) = 1 :=
  localFrame_normalized p.primeCompl (infinityFrame A B) _ (infinityFrame_dx A B)

/-- Exact compatibility with the original integral differential frame, not a separate choice. -/
theorem affinePrimeFrame_map (A B : R) (i : Fin 2)
    (p : Ideal (AffineChart A B i)) [p.IsPrime]
    (ω : KaehlerDifferential R (AffineChart A B i)) :
    affinePrimeFrame A B i p (KaehlerDifferential.map R R (AffineChart A B i) (Localization.AtPrime p) ω) =
      algebraMap (AffineChart A B i) (Localization.AtPrime p) (affineFrame A B i ω) :=
  localFrame_map p.primeCompl (affineFrame A B i) ω

theorem infinityPrimeFrame_map (A B : R)
    (p : Ideal (InfinityChart318.SmoothRing A B)) [p.IsPrime]
    (ω : KaehlerDifferential R (InfinityChart318.SmoothRing A B)) :
    infinityPrimeFrame A B p
      (KaehlerDifferential.map R R (InfinityChart318.SmoothRing A B) (Localization.AtPrime p) ω) =
      algebraMap (InfinityChart318.SmoothRing A B) (Localization.AtPrime p) (infinityFrame A B ω) :=
  localFrame_map p.primeCompl (infinityFrame A B) ω

@[expose] def affinePrimeDerivation (A B : R) (i : Fin 2)
    (p : Ideal (AffineChart A B i)) [p.IsPrime] : Derivation R (Localization.AtPrime p) (Localization.AtPrime p) :=
  KaehlerDifferential.linearMapEquivDerivation R (Localization.AtPrime p) (affinePrimeFrame A B i p).toLinearMap

@[expose] def infinityPrimeDerivation (A B : R)
    (p : Ideal (InfinityChart318.SmoothRing A B)) [p.IsPrime] :
    Derivation R (Localization.AtPrime p) (Localization.AtPrime p) :=
  KaehlerDifferential.linearMapEquivDerivation R (Localization.AtPrime p) (infinityPrimeFrame A B p).toLinearMap

/-- The actual prime-local derivation extends the actual chart derivation. -/
theorem affinePrimeDerivation_map (A B : R) (i : Fin 2)
    (p : Ideal (AffineChart A B i)) [p.IsPrime] (s : AffineChart A B i) :
    affinePrimeDerivation A B i p (algebraMap (AffineChart A B i) (Localization.AtPrime p) s) =
      algebraMap (AffineChart A B i) (Localization.AtPrime p) (affineDerivation A B i s) := by
  exact localFrame_D p.primeCompl (affineFrame A B i) s

theorem infinityPrimeDerivation_map (A B : R)
    (p : Ideal (InfinityChart318.SmoothRing A B)) [p.IsPrime] (s : InfinityChart318.SmoothRing A B) :
    infinityPrimeDerivation A B p (algebraMap (InfinityChart318.SmoothRing A B) (Localization.AtPrime p) s) =
      algebraMap (InfinityChart318.SmoothRing A B) (Localization.AtPrime p) (infinityDerivation A B s) := by
  exact localFrame_D p.primeCompl (infinityFrame A B) s

end WeierstrassPrimeFrames318
