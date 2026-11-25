module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section
noncomputable section

namespace OriginalActualRegularMapAtComplexChart318

open AlgebraicGeometry CategoryTheory
universe u
local notation "C" => CommRingCat.of ℂ
local notation "P" => Spec C

variable {R B : Type} [CommRing R] [CommRing B]
local notation "SR" => Spec (CommRingCat.of R)
local notation "SB" => Spec (CommRingCat.of B)

def fieldClosedPoint : P := (⟨(⊥ : Ideal ℂ), inferInstance⟩ : PrimeSpectrum ℂ)

def point (p : R →+* ℂ) : P ⟶ SR := Spec.map (CommRingCat.ofHom p)

def localizationArrow (s : R) :
    Spec (CommRingCat.of (Localization.Away s)) ⟶ SR :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s)))

theorem point_in_basic (p : R →+* ℂ) (s : R) :
    point p fieldClosedPoint ∈ PrimeSpectrum.basicOpen s ↔ p s ≠ 0 := by
  rw [PrimeSpectrum.mem_basicOpen]
  change s ∉ Ideal.comap p ⊥ ↔ _
  rw [Ideal.mem_comap, Submodule.mem_bot]

instance localization_open (s : R) : IsOpenImmersion (localizationArrow s) :=
  inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away s)))))

theorem localization_range (s : R) :
    Set.range (localizationArrow s) = (PrimeSpectrum.basicOpen s : Set SR) := by
  change ((localizationArrow s).opensRange : Set SR)=_
  rw [localizationArrow, Scheme.Hom.opensRange_localizationAway]

variable {X : Scheme} (j : SB ⟶ X) [IsOpenImmersion j]

/-- Choose the one actual principal localization through the point
on which the true map factors through the specified target chart.
This is a Scheme factorization, not a chart of numerical values. -/
theorem actual_local_ring (f : SR ⟶ X) (p : R →+* ℂ)
    (hp : (point p≫f) fieldClosedPoint ∈ Set.range j) :
    ∃ (s : R) (l : Spec (CommRingCat.of (Localization.Away s)) ⟶ SB),
      p s≠0 ∧ l≫j=localizationArrow s≫f := by
  let U : Set SR := f ⁻¹' Set.range j
  have openU : IsOpen U := j.isOpenEmbedding.isOpen_range.preimage f.continuous
  have pin : point p fieldClosedPoint ∈ U := hp
  obtain ⟨_,⟨s,rfl⟩, H,sub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp openU _ pin
  have h : Set.range (localizationArrow s≫f) ⊆ Set.range j := by
    rintro _ ⟨x,rfl⟩
    have xmem : localizationArrow s x ∈ PrimeSpectrum.basicOpen s :=
      (localization_range s) ▸ (Set.mem_range_self x : localizationArrow s x ∈ Set.range (localizationArrow s))
    exact sub xmem
  exact ⟨s,IsOpenImmersion.lift j (localizationArrow s≫f) h,(point_in_basic p s).1 H,
    IsOpenImmersion.lift_fac _ _ _⟩

variable (s : R)
local notation "SLoc" => Spec (CommRingCat.of (Localization.Away s))

def localValue (p : R →+* ℂ) (hp : p s≠0) : Localization.Away s →+* ℂ :=
  IsLocalization.Away.lift s (isUnit_iff_ne_zero.2 hp)

theorem localValue_algebraMap (p : R →+* ℂ) (hp : p s≠0) (r : R) :
    localValue s p hp (algebraMap R (Localization.Away s) r)=p r :=
  IsLocalization.Away.lift_eq s (isUnit_iff_ne_zero.2 hp) r

def localPoint (p : R →+* ℂ) (hp : p s≠0) : P ⟶ SLoc :=
  Spec.map (CommRingCat.ofHom (localValue s p hp))

theorem localPoint_returns (p : R→+*ℂ) (hp : p s≠0) :
    localPoint s p hp≫localizationArrow s=point p := by
  have h : (localValue s p hp).comp (algebraMap R (Localization.Away s))=p :=
    RingHom.ext (localValue_algebraMap s p hp)
  unfold localPoint localizationArrow point
  rw [←Spec.map_comp,←CommRingCat.ofHom_comp,h]

variable (l : SLoc ⟶ SB)

def coordinateMap : B →+* Localization.Away s := (Spec.preimage l).hom

theorem exact_field_read (p : R→+*ℂ) (hp : p s≠0) (b : B) :
    (Spec.preimage (localPoint s p hp≫l)).hom b=localValue s p hp (coordinateMap s l b) := by
  have arr :
      Spec.map (CommRingCat.ofHom ((localValue s p hp).comp (coordinateMap s l))) =
        localPoint s p hp≫l := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    change localPoint s p hp≫Spec.map (Spec.preimage l)=_
    rw [Spec.map_preimage]
  rw [←arr,Spec.preimage_map]
  rfl

/-- The genuine field values of every target coordinate are those of
one actual rational function, everywhere on the same basic open. -/
theorem actual_coordinate_fraction (b : B) :
    ∃ (m : ℕ) (r : R), ∀ (p : R→+*ℂ) (hp : p s≠0),
      (Spec.preimage (localPoint s p hp≫l)).hom b=p r/(p s)^m := by
  obtain ⟨m,r,hr⟩ := IsLocalization.Away.surj (S:=Localization.Away s) (x:=s) (coordinateMap s l b)
  refine ⟨m,r,?_⟩
  intro p hp
  rw [exact_field_read]
  apply (eq_div_iff (pow_ne_zero m hp)).2
  have e := congrArg (localValue s p hp) hr
  simpa only [map_mul,map_pow,localValue_algebraMap] using e

/-- The localization field evaluation returns exactly the original
map followed by its target chart inclusion. -/
theorem same_whole_map (f : SR ⟶ X) (h : l≫j=localizationArrow s≫f)
    (p : R→+*ℂ) (hp : p s≠0) :
    (localPoint s p hp≫l)≫j=point p≫f := by
  rw [Category.assoc,h,←Category.assoc,localPoint_returns]

end OriginalActualRegularMapAtComplexChart318
