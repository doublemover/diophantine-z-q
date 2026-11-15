module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Finiteness.Basic
public section
noncomputable section
namespace NormalFiniteImageDetection318
variable {R S K L:Type*} [CommRing R] [CommRing S] [CommRing K] [CommRing L]
  [Algebra R S] [Algebra R K] [Algebra R L]
  [IsFractionRing R K] [IsIntegrallyClosed R] [Module.Finite R S]
  (e:S→ₐ[R]L) (k:K→ₐ[R]L)

/-- A normal finite base ring is detected inside its integral extension
by the exact image of its fraction field in a common overring. Both
embeddings and their actual R-algebra structures are retained. -/
theorem range_iff (he:Function.Injective e) (hk:Function.Injective k) (x:S):
    x∈Set.range (algebraMap R S) ↔ e x∈Set.range k:=by
  letI:Algebra.IsIntegral R S:=Algebra.IsIntegral.of_finite R S
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨algebraMap R K r,(k.commutes r).trans (e.commutes r).symm⟩
  · rintro ⟨z,hz⟩
    have hi:IsIntegral R (e x):=IsIntegral.map e (Algebra.IsIntegral.isIntegral x)
    have hzI:IsIntegral R z:=(isIntegral_algHom_iff k hk).mp (hz.symm ▸ hi)
    obtain ⟨r,hr⟩:=IsIntegrallyClosed.algebraMap_eq_of_integral hzI
    refine ⟨r,he ?_⟩
    rw [e.commutes,←k.commutes r,hr,hz]
end NormalFiniteImageDetection318
