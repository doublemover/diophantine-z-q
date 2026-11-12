module
public import FourRootInfinityCoordinateRing318
public import FourRootGluedScheme318
public import ThreeBranchLegendreInfinityAlgebra318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace FourRootCharacterInfinityOpen318
open AlgebraicGeometry CategoryTheory
open FourRootInfinityCoordinateRing318
set_option maxHeartbeats 800000
variable (b:Fin 4→ℂ) (k:Fin 3→Fin 4)

/-- Invert only the original three sign ratios used by this character.
Their product is nonzero at EVERY point over infinity, not just a selected
branch. Its vanishing away from infinity is not silently excluded globally. -/
@[expose] def denominator:Ring b:=
  coordinate b (some (k 0))*coordinate b (some (k 1))*coordinate b (some (k 2))
abbrev OpenRing:=Localization.Away (denominator b k)
@[expose] def u:OpenRing b k:=algebraMap (Ring b) (OpenRing b k) (coordinate b none)
lemma denominator_unit:IsUnit (algebraMap (Ring b) (OpenRing b k) (denominator b k)):=
  IsLocalization.Away.isUnit_of_dvd (denominator b k) (dvd_refl _)
@[expose] def rootUnit:(OpenRing b k)ˣ:=(denominator_unit b k).unit
lemma rootUnit_val:(rootUnit b k:OpenRing b k)=
    algebraMap (Ring b) (OpenRing b k) (denominator b k):=
  (denominator_unit b k).unit_spec

lemma square:
    (rootUnit b k:OpenRing b k)^2=
      (1+algebraMap ℂ (OpenRing b k) (b 0-b (k 0))*u b k^2)*
      (1+algebraMap ℂ (OpenRing b k) (b 0-b (k 1))*u b k^2)*
      (1+algebraMap ℂ (OpenRing b k) (b 0-b (k 2))*u b k^2):=by
  rw [rootUnit_val]
  have h:denominator b k^2=
      (1+algebraMap ℂ (Ring b) (b 0-b (k 0))*coordinate b none^2)*
      (1+algebraMap ℂ (Ring b) (b 0-b (k 1))*coordinate b none^2)*
      (1+algebraMap ℂ (Ring b) (b 0-b (k 2))*coordinate b none^2):=by
    simp only [denominator,mul_pow,relation]
  have he:=congrArg (algebraMap (Ring b) (OpenRing b k)) h
  simpa only [map_mul,map_pow,map_add,map_one,
    ←IsScalarTower.algebraMap_apply ℂ (Ring b) (OpenRing b k),u] using he

/-- Actual principal open subscheme of the old infinity chart. -/
@[expose] def inclusion:Spec (CommRingCat.of (OpenRing b k))⟶
    FourRootGluedScheme318.infinityScheme b:=
  Spec.map (CommRingCat.ofHom (algebraMap (Ring b) (OpenRing b k)))
instance inclusion_open:IsOpenImmersion (inclusion b k):=
  IsOpenImmersion.of_isLocalization (denominator b k)

/-- The localization retains all scheme points over u=0, including
non-complex residue fields. Each ratio squares to1 in the residue field. -/
lemma denominator_not_mem (p:PrimeSpectrum (Ring b))
    (hu:coordinate b none∈p.asIdeal):denominator b k∉p.asIdeal:=by
  have hn:∀j:Fin 3,coordinate b (some (k j))∉p.asIdeal:=by
    intro j hj
    have hs:coordinate b (some (k j))^2∈p.asIdeal:=by
      simpa only [pow_two] using p.asIdeal.mul_mem_left (coordinate b (some (k j))) hj
    have ht:algebraMap ℂ (Ring b) (b 0-b (k j))*coordinate b none^2∈p.asIdeal:=by
      simpa only [pow_two] using p.asIdeal.mul_mem_left
        (algebraMap ℂ (Ring b) (b 0-b (k j)))
        (p.asIdeal.mul_mem_left (coordinate b none) hu)
    have he:=p.asIdeal.add_mem (p.asIdeal.neg_mem ht) hs
    have hone:(1:Ring b)∈p.asIdeal:=by
      convert he using 1
      rw [relation]
      ring
    exact p.isPrime.ne_top (p.asIdeal.eq_top_iff_one.mpr hone)
  intro h
  change coordinate b (some (k 0))*coordinate b (some (k 1))*
    coordinate b (some (k 2))∈p.asIdeal at h
  have hmul:=p.isPrime.mem_or_mem h
  rcases hmul with h|h
  · rcases p.isPrime.mem_or_mem h with h|h
    · exact hn 0 h
    · exact hn 1 h
  · exact hn 2 h

lemma point_denominator_nonzero (f:Ring b→ₐ[ℂ]ℂ)
    (hu:f (coordinate b none)=0):f (denominator b k)≠0:=by
  have hn:∀j:Fin 3,f (coordinate b (some (k j)))≠0:=by
    intro j hj
    have h:=congrArg f (relation b (k j))
    simp only [map_pow,map_add,map_one,map_mul,hu,hj,zero_pow (by decide:2≠0),
      mul_zero,add_zero] at h
    exact zero_ne_one h
  simpa only [denominator,map_mul] using mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2)

@[expose] def pointLift (f:Ring b→ₐ[ℂ]ℂ) (hu:f (coordinate b none)=0):
    OpenRing b k→ₐ[ℂ]ℂ:=
  IsLocalization.Away.liftAlgHom (f:=f) (denominator b k)
    (isUnit_iff_ne_zero.mpr (point_denominator_nonzero b k f hu))
lemma pointLift_on_ring (f:Ring b→ₐ[ℂ]ℂ) (hu:f (coordinate b none)=0) (x:Ring b):
    pointLift b k f hu (algebraMap (Ring b) (OpenRing b k) x)=f x:=by
  simp only [pointLift,IsLocalization.Away.liftAlgHom_apply]
lemma pointLift_u (f:Ring b→ₐ[ℂ]ℂ) (hu:f (coordinate b none)=0):
    pointLift b k f hu (u b k)=0:=by
  rw [u,pointLift_on_ring,hu]

end FourRootCharacterInfinityOpen318
