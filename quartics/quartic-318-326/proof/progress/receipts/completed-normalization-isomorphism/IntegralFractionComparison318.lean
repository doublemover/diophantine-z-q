module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section
namespace IntegralFractionComparison318
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B K:Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [Field K] [Algebra A K] [IsFractionRing A K]

/-- An integral intermediate ring embedded in the actual fraction field of
a normal domain is that domain, with the specified coefficient map. -/
theorem bijective (f:A→+*B) (hf:f.IsIntegral) (j:B→+*K)
    (hj:Function.Injective j) (hs:j.comp f=algebraMap A K):Function.Bijective f:=by
  letI:Algebra A B:=f.toAlgebra
  letI:Algebra B K:=j.toAlgebra
  letI:IsScalarTower A B K:=IsScalarTower.of_algebraMap_eq' hs.symm
  constructor
  · intro a b hab
    apply IsFractionRing.injective A K
    rw [←hs]
    exact congrArg j hab
  · intro b
    have hb:IsIntegral A b:=hf b
    have hk:IsIntegral A (j b):=hb.map (IsScalarTower.toAlgHom A B K)
    obtain ⟨a,ha⟩:=IsIntegrallyClosed.algebraMap_eq_of_integral hk
    refine ⟨a,hj ?_⟩
    rw [←ha]
    exact RingHom.congr_fun hs a
end IntegralFractionComparison318
