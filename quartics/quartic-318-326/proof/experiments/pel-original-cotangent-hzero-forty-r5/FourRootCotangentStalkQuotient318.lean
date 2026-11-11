module
public import FourRootAffineCotangentIdeal318
public import AffineTildeQuotientStalk318
public import OpenImmersionStalkLength318
public section
noncomputable section
namespace FourRootCotangentStalkQuotient318
open AlgebraicGeometry CategoryTheory
open FourRootIntrinsicCanonicalFrames318
universe u
/-- An actual affine sheaf comparison gives length equality at EVERY
prime of the chart. The ambient stalk and its canonical local-ring
module action are retained on the left. -/
theorem chart_length {X : Scheme.{u}} {R : Type u} [CommRing R]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (I : Ideal R)
    (e : M.restrict j ≅ AffineTildeQuotientStalk318.QuotientSheaf R I)
    (p : PrimeSpectrum R) :
    Module.length (X.presheaf.stalk (j p)) (CanonicalStalkModule318.stalk M (j p)) =
      Module.length (AffineTildeQuotientStalk318.LocalRing R p)
        (AffineTildeQuotientStalk318.LocalRing R p ⧸
          AffineTildeQuotientStalk318.localIdeal R I p) :=
  (OpenImmersionStalkLength318.length_eq j M p).symm.trans
    ((CanonicalStalkModule318.length_iso e p).trans
      (AffineTildeQuotientStalk318.length_eq R I p))
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
/-- True stalk length of the original global relative cotangent sheaf
at an actual point of the original glued scheme. -/
@[expose] def length (p : FourRootGluedScheme318.scheme b) : ℕ∞ :=
  Module.length ((FourRootGluedScheme318.scheme b).presheaf.stalk p)
    (CanonicalStalkModule318.stalk (FourRootGlobalRelativeCotangent318.omega b) p)
/-- ALL finite-chart primes, not just complex points or branch primes. -/
theorem finite_length (i : Fin 4) (p : PrimeSpectrum (FiniteRing b i)) :
    length b (finiteEmbedding b i p) =
      Module.length (AffineTildeQuotientStalk318.LocalRing (FiniteRing b i) p)
        (AffineTildeQuotientStalk318.LocalRing (FiniteRing b i) p ⧸
          AffineTildeQuotientStalk318.localIdeal (FiniteRing b i)
            (FourRootDerivativeZeroCotangent318.finiteZeroIdeal b i) p) :=
  chart_length (finiteEmbedding b i) (FourRootGlobalRelativeCotangent318.omega b)
    (FourRootDerivativeZeroCotangent318.finiteZeroIdeal b i)
    (FourRootAffineCotangentIdeal318.finiteIso b hb i) p
/-- ALL primes in the canonical infinity open, retaining every center
and the original reciprocal base coordinate. -/
theorem infinity_length (p : PrimeSpectrum (InfinityRing b hb)) :
    length b (infinityEmbedding b hb p) =
      Module.length (AffineTildeQuotientStalk318.LocalRing (InfinityRing b hb) p)
        (AffineTildeQuotientStalk318.LocalRing (InfinityRing b hb) p ⧸
          AffineTildeQuotientStalk318.localIdeal (InfinityRing b hb)
            (FourRootDerivativeZeroCotangent318.infinityZeroIdeal b hb) p) :=
  chart_length (infinityEmbedding b hb) (FourRootGlobalRelativeCotangent318.omega b)
    (FourRootDerivativeZeroCotangent318.infinityZeroIdeal b hb)
    (FourRootAffineCotangentIdeal318.infinityIso b hb) p
end FourRootCotangentStalkQuotient318
