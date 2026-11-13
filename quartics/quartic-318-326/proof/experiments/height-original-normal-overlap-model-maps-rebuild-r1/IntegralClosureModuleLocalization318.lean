module
public import IntegralClosurePrincipalLocalization318
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace IntegralClosureModuleLocalization318
variable {P Q B : Type*} [CommRing P] [CommRing Q] [CommRing B]
  [Algebra P Q] [Algebra P B] [Algebra Q B] [IsScalarTower P Q B]
  (s : P) [IsLocalization.Away s Q]
local notation "N" => integralClosure P B
local notation "O" => integralClosure Q B
local notation "i" => IntegralClosureLocalizationMap318.inclusion (P:=P) (Q:=Q) (B:=B)

/-- The SAME ambient inclusion localizes the entire old normal order as
a P-module. The denominator set is powers of s, not all source units. -/
lemma localization : IsLocalizedModule (Submonoid.powers s) i.toLinearMap := by
  letI := IntegralClosureLocalizationMap318.normalAlgebra (P:=P) (Q:=Q) (B:=B)
  letI := IntegralClosureLocalizationMap318.baseTower (P:=P) (Q:=Q) (B:=B)
  letI : IsLocalization (Algebra.algebraMapSubmonoid N (Submonoid.powers s)) O := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      IntegralClosurePrincipalLocalization318.localization (Q:=Q) (B:=B) s
  exact (isLocalizedModule_iff_isLocalization (S:=Submonoid.powers s)
    (A:=N) (Aₛ:=O)).mpr inferInstance

include s in
lemma baseChange : IsBaseChange Q i.toLinearMap := by
  letI := localization (Q:=Q) (B:=B) s
  exact IsLocalizedModule.isBaseChange (Submonoid.powers s) Q i.toLinearMap
end IntegralClosureModuleLocalization318
