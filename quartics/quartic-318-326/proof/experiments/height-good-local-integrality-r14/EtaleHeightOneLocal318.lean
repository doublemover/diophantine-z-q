module
public import HeightOneDVR318
public import EtaleLocalDVR318
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Flat.Localization
public section
noncomputable section
namespace EtaleHeightOneLocal318
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 800000
variable (A B : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
  [CommRing B] [Algebra A B] [Algebra.Etale A B]
  (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]

local instance localizedAlgebra :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
  Localization.AtPrime.algebraOfLiesOver p q

local instance localizedLocalHom :
    IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
  rw [Localization.AtPrime.algebraMap_eq p q]
  infer_instance

local instance localizedFinite :
    Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
  Algebra.EssFiniteType.of_comp A (Localization.AtPrime p) (Localization.AtPrime q)

local instance localizedUnramified :
    Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
  Algebra.FormallyUnramified.of_restrictScalars A (Localization.AtPrime p) (Localization.AtPrime q)

/-- The actual local ring upstairs is a domain even if the etale order splits. -/
theorem local_domain (hp : p.height = 1) : IsDomain (Localization.AtPrime q) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime p) := HeightOneDVR318.localization p hp
  exact EtaleLocalDVR318.domain (Localization.AtPrime p) (Localization.AtPrime q)

/-- Local DVR construction for every actual prime over a height-one base prime.
No domain or DVR structure on the etale target is assumed. -/
theorem local_dvr (hp : p.height = 1) :
    letI := local_domain A B p q hp
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime p) := HeightOneDVR318.localization p hp
  exact EtaleLocalDVR318.dvr (Localization.AtPrime p) (Localization.AtPrime q)

end EtaleHeightOneLocal318
