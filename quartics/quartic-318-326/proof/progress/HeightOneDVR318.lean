module
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Tactic
public section
noncomputable section
namespace HeightOneDVR318
set_option maxHeartbeats 600000
open Ring
variable {R:Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- The actual height-one localization of a normal Noetherian domain is a DVR.
No DVR or regular-local structure on the localization is supplied. -/
theorem localization (p:Ideal R) [p.IsPrime] (hp:p.height=1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  let S:=Localization.AtPrime p
  letI:IsIntegrallyClosed S:=isIntegrallyClosed_of_isLocalization S p.primeCompl
    p.primeCompl_le_nonZeroDivisors
  letI:IsNoetherianRing S:=IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  have hd:ringKrullDim S=1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S,hp]
    rfl
  letI:Ring.KrullDimLE 1 S:=(Ring.krullDimLE_iff).mpr (le_of_eq hd)
  letI:Ring.DimensionLEOne S:=⟨fun hq hqp=>hqp.isMaximal_of_ne_bot hq⟩
  letI:IsDedekindRing S:=
    { (inferInstance:IsNoetherianRing S), (inferInstance:Ring.DimensionLEOne S),
      (inferInstance:IsIntegralClosure S S (FractionRing S)) with }
  have hn:¬IsField S:=IsLocalization.AtPrime.not_isField R (Ideal.ne_bot_of_height_eq_one hp) S
  exact ((IsDiscreteValuationRing.TFAE S hn).out 1 3).mpr (inferInstance:IsDedekindDomain S)

end HeightOneDVR318
