module
public import ThreeJGlobalDifferentialJoin318
public import Mathlib.RingTheory.Localization.Ideal
public section
noncomputable section
namespace PrincipalLocalizationIdealRecovery318
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
set_option maxHeartbeats 900000

/-- If the localization parameter is a unit modulo the actual ideal,
localizing and contracting recovers the whole ideal, not merely its radical. -/
theorem recover (x : A) [IsLocalization.Away x B] (I : Ideal A)
    (hx : IsUnit (Ideal.Quotient.mk I x)) :
    (I.map (algebraMap A B)).comap (algebraMap A B)=I := by
  ext a
  change algebraMap A B a ∈ I.map (algebraMap A B) ↔ a ∈ I
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers x)]
  constructor
  · rintro ⟨m,⟨n,rfl⟩,hm⟩
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    rw [map_mul,map_pow] at hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (hx.pow n).mul_left_cancel
    simpa only [mul_zero] using hz
  · intro ha
    exact ⟨1,Submonoid.one_mem _,by simpa only [one_mul] using ha⟩

/-- Entire ideal equality follows from localization equality and the two
explicit quotient-unit conditions. Multiplicities are preserved. -/
theorem eq_of_localized (x : A) [IsLocalization.Away x B] (I J : Ideal A)
    (hI : IsUnit (Ideal.Quotient.mk I x)) (hJ : IsUnit (Ideal.Quotient.mk J x))
    (h : I.map (algebraMap A B)=J.map (algebraMap A B)) : I=J := by
  rw [←recover (B:=B) x I hI,←recover (B:=B) x J hJ,h]
end PrincipalLocalizationIdealRecovery318
