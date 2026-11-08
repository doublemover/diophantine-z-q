module
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace LocalizationSourceTransport318
set_option maxHeartbeats 500000
variable {R S T:Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R T] [Algebra S T]

/-- Transport an actual principal localization along a proved source-ring
isomorphism, with the specified target algebra maps. -/
theorem away (e:R≃+*S) (d:R) [IsLocalization.Away (e d) T]
    (he:∀r,algebraMap R T r=algebraMap S T (e r)) : IsLocalization.Away d T:=by
  apply IsLocalization.Away.mk d
  · rw [he]
    exact IsLocalization.Away.algebraMap_isUnit (S:=T) (e d)
  · intro z
    obtain ⟨n,s,hs⟩:=IsLocalization.Away.surj (e d) z
    refine ⟨n,e.symm s,?_⟩
    simpa only [he,RingEquiv.apply_symm_apply] using hs
  · intro a b hab
    rw [he,he] at hab
    obtain ⟨n,hn⟩:=IsLocalization.Away.exists_of_eq (e d) hab
    refine ⟨n,e.injective ?_⟩
    simpa only [map_mul,map_pow] using hn

end LocalizationSourceTransport318
