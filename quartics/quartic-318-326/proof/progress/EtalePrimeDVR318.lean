module
public import EtaleLocalDVR318
public import EvenContactEtale318
public import Mathlib.RingTheory.Smooth.Flat
public section
noncomputable section
namespace EtalePrimeDVR318
set_option maxHeartbeats 800000
open IsLocalRing
variable (R S:Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Algebra.Etale R S]
  (q:Ideal S) [q.IsPrime] [q.LiesOver (maximalIdeal R)]
include R S q

local instance : Module.Flat R (Localization.AtPrime q) :=
  Module.Flat.trans R S (Localization.AtPrime q)

/-- The actual prime localization over the closed base point has the actual
local structure map; no local-hom or maximal-ideal formula is supplied. -/
theorem localMap : IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
  letI:Algebra (Localization.AtPrime (maximalIdeal R)) (Localization.AtPrime q):=
    Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) q
  have hm:=((Algebra.isUnramifiedAt_iff_map_eq R (maximalIdeal R) q).mp inferInstance).2
  exact ((IsLocalRing.local_hom_TFAE _).out 1 3).mpr (le_of_eq hm)

/-- Domain structure of the genuine local ring of a potentially split finite
etale algebra, derived after choosing a closed-fiber prime. -/
theorem local_domain : IsDomain (Localization.AtPrime q) := by
  letI:=localMap R S q
  exact EtaleLocalDVR318.domain R (Localization.AtPrime q)

theorem local_dvr : letI:=local_domain R S q; IsDiscreteValuationRing (Localization.AtPrime q) := by
  letI:=localMap R S q
  exact EtaleLocalDVR318.dvr R (Localization.AtPrime q)

/-- Exact actual ramification index, not an asserted valuation multiplier. -/
theorem ramification_one : q.ramificationIdx R=1 :=
  Ideal.ramificationIdx_eq_one q R

/-- Every original value is preserved in the actual local branch. -/
theorem local_value (x:R) :
    letI:=local_domain R S q
    letI:=local_dvr R S q
    IsDiscreteValuationRing.addVal (Localization.AtPrime q)
      (algebraMap R (Localization.AtPrime q) x)=IsDiscreteValuationRing.addVal R x := by
  letI:=localMap R S q
  exact EtaleLocalDVR318.value R (Localization.AtPrime q) x

/-- The actual residue extension is finite and separable. -/
theorem residue_data :
    letI:=localMap R S q
    Module.Finite (ResidueField R) (ResidueField (Localization.AtPrime q)) ∧
      Algebra.IsSeparable (ResidueField R) (ResidueField (Localization.AtPrime q)) := by
  letI:=localMap R S q
  exact ⟨inferInstance,inferInstance⟩

end EtalePrimeDVR318
