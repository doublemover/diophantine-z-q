module
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public section
noncomputable section
namespace IntegralClosureTransport318

/-- Transport both the order and its normalization along actual compatible
ring equivalences, retaining the same ambient algebra. -/
theorem transport {R R' A A' K:Type*}
    [CommRing R] [CommRing R'] [CommRing A] [CommRing A'] [CommRing K]
    [Algebra R K] [Algebra R' K] [Algebra A K] [Algebra A' K]
    [IsIntegralClosure A' R' K]
    (e:R≃+*R') (d:A≃+*A')
    (he:(algebraMap R' K).comp e.toRingHom=algebraMap R K)
    (hd:∀a:A,algebraMap A K a=algebraMap A' K (d a)) :
    IsIntegralClosure A R K where
  algebraMap_injective:=by
    intro a b h
    apply d.injective
    apply IsIntegralClosure.algebraMap_injective A' R' K
    simpa only [←hd] using h
  isIntegral_iff:=by
    intro x
    rw [e.isIntegral_iff he x,IsIntegralClosure.isIntegral_iff (A:=A')]
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨d.symm a,by rw [hd,d.apply_symm_apply,ha]⟩
    · rintro ⟨a,ha⟩
      exact ⟨d a,by rw [←hd,ha]⟩

end IntegralClosureTransport318
