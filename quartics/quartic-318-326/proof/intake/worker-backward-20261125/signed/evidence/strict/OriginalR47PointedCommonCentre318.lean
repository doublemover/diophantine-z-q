module
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.DiscreteSubset
public section
noncomputable section

namespace OriginalR47PointedCommonCentre318

open PrimeSpectrum Set TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra C B]

/-- The actual fibre of an affine unramified finite-type chart over a
closed point, with no claim that the original whole fibre is singleton. -/
theorem discrete_closed_fibre [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B] (p : Ideal A) [p.IsMaximal] :
    IsDiscrete (zeroLocus ((p.map (algebraMap A B) : Ideal B) : Set B)) := by
  let T := B ⧸ p.map (algebraMap A B)
  let k := A ⧸ p
  let : Field k := Ideal.Quotient.field p
  let : Module.Finite k T := Algebra.FormallyUnramified.finite_of_free k T
  let : IsArtinianRing T := isArtinian_of_tower k inferInstance
  let : DiscreteTopology (PrimeSpectrum T) :=
    discreteTopology_iff_finite_and_krullDimLE_zero.mpr
      ⟨inferInstance,.mk₀ fun M hM => (IsArtinianRing.isPrime_iff_isMaximal M).mp hM⟩
  let g := Ideal.Quotient.mk (p.map (algebraMap A B))
  have h := (isDiscrete_univ_iff.mpr (inferInstance : DiscreteTopology (PrimeSpectrum T))).image
    (isEmbedding_comap_of_surjective _ g Ideal.Quotient.mk_surjective).isInducing
  have hker : RingHom.ker g = p.map (algebraMap A B) := Ideal.mk_ker
  rwa [Set.image_univ, range_comap_of_surjective _ g Ideal.Quotient.mk_surjective, hker] at h

/-- This equality of supports is tied to the exact composite of chosen
ring maps, not an independently chosen closed immersion. -/
theorem map_support {D : Type u} [CommRing D] (f : B →+* D) (J : Ideal B) (z : PrimeSpectrum D) :
    z ∈ zeroLocus ((J.map f : Ideal D) : Set D) ↔ comap f z ∈ zeroLocus (J : Set B) := by
  change J.map f ≤ z.asIdeal ↔ J ≤ z.asIdeal.comap f
  exact Ideal.map_le_iff_le_comap

variable (p : Ideal A) [p.IsMaximal] (r : Ideal C) [r.IsMaximal]
variable (u₀ : PrimeSpectrum B)
variable (hp : comap (algebraMap A B) u₀ = ⟨p,inferInstance⟩)
variable (hr : comap (algebraMap C B) u₀ = ⟨r,inferInstance⟩)

abbrev first : Ideal B := p.map (algebraMap A B)
abbrev second : Ideal B := r.map (algebraMap C B)
abbrev further (g : B) := algebraMap B (Localization.Away g)

structure Window where
  g : B
  point : PrimeSpectrum (Localization.Away g)
  read : comap (further g) point = u₀
  oldSupport : zeroLocus (((first (B:=B) p).map (further g) : Ideal _) : Set _) = {point}
  splitSupport : zeroLocus (((second (B:=B) r).map (further g) : Ideal _) : Set _) = {point}

include hp hr in
/-- Choose one single genuine common affine window around the original
point; only its two *restricted* scheme-theoretic fibres have singleton
underlying support. The unrestricted chart may have many such points. -/
theorem window [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    [Algebra.EssFiniteType C B] [Algebra.FormallyUnramified C B] :
    Nonempty (Window p r u₀) := by
  have hup : u₀ ∈ zeroLocus (first (B:=B) p : Set B) := (map_support _ p u₀).mpr (by
    rw [hp]
    change p ≤ p
    exact le_rfl)
  have hur : u₀ ∈ zeroLocus (second (B:=B) r : Set B) := (map_support _ r u₀).mpr (by
    rw [hr]
    change r ≤ r
    exact le_rfl)
  obtain ⟨U,hU,hUread⟩ := (isDiscrete_iff_forall_mem_exists_isOpen.mp
    (discrete_closed_fibre (A:=A) (B:=B) p)) u₀ hup
  obtain ⟨V,hV,hVread⟩ := (isDiscrete_iff_forall_mem_exists_isOpen.mp
    (discrete_closed_fibre (A:=C) (B:=B) r)) u₀ hur
  have hUV : u₀ ∈ U ∩ V := by
    have h₁ : u₀ ∈ U ∩ zeroLocus (first (B:=B) p : Set B) := by simp only [hUread,Set.mem_singleton_iff]
    have h₂ : u₀ ∈ V ∩ zeroLocus (second (B:=B) r : Set B) := by simp only [hVread,Set.mem_singleton_iff]
    exact ⟨h₁.1,h₂.1⟩
  obtain ⟨_,⟨g,rfl⟩,hg,hsub⟩ :=
    (isTopologicalBasis_basic_opens (R:=B)).exists_subset_of_mem_open hUV (hU.inter hV)
  have hrange := localization_away_comap_range (Localization.Away g) g
  have huRange : u₀ ∈ Set.range (comap (further g)) := by
    rw [hrange]
    exact hg
  obtain ⟨v,hv⟩ := huRange
  have hinj := localization_comap_injective (Localization.Away g) (Submonoid.powers g)
  refine ⟨⟨g,v,hv,?_,?_⟩⟩
  · ext z
    rw [map_support]
    constructor
    · intro hz
      have hz' : comap (further g) z ∈ (basicOpen g : Set (PrimeSpectrum B)) :=
        hrange ▸ (Set.mem_range_self (f := comap (further g)) z)
      have hz₀ : comap (further g) z ∈ U ∩ zeroLocus (first (B:=B) p : Set B) :=
        ⟨(hsub hz').1,hz⟩
      rw [hUread,Set.mem_singleton_iff] at hz₀
      exact Set.mem_singleton_iff.mpr (hinj (hz₀.trans hv.symm))
    · rintro rfl
      exact hv.symm ▸ hup
  · ext z
    rw [map_support]
    constructor
    · intro hz
      have hz' : comap (further g) z ∈ (basicOpen g : Set (PrimeSpectrum B)) :=
        hrange ▸ (Set.mem_range_self (f := comap (further g)) z)
      have hz₀ : comap (further g) z ∈ V ∩ zeroLocus (second (B:=B) r : Set B) :=
        ⟨(hsub hz').2,hz⟩
      rw [hVread,Set.mem_singleton_iff] at hz₀
      exact Set.mem_singleton_iff.mpr (hinj (hz₀.trans hv.symm))
    · rintro rfl
      exact hv.symm ▸ hur

/-- Compose with the literal chosen principal localization, so the
support statement upgrades to equality of the two actual ideals. -/
theorem radial_after_away [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (g : B) :
    ((first (B:=B) p).map (further g)).IsRadical := by
  let J : Ideal B := first (B:=B) p
  have hJ : J.IsRadical := Algebra.FormallyUnramified.isRadical_map_isMaximal A B p
  apply Ideal.radical_eq_iff.mp
  change (J.map (further g)).radical = J.map (further g)
  exact (IsLocalization.map_radical (S := Localization.Away g) (Submonoid.powers g) J).symm.trans
    (congrArg (Ideal.map (further g)) hJ.radical)

theorem ideal_eq_point {D : Type u} [CommRing D] (J : Ideal D) (z : PrimeSpectrum D)
    (hJ : J.IsRadical) (h : zeroLocus (J : Set D) = {z}) :
    J = z.asIdeal := by
  have hz : J ≤ z.asIdeal := by
    change z ∈ zeroLocus (J : Set D)
    rw [h]
    exact Set.mem_singleton _
  have hz' : zeroLocus (z.asIdeal : Set D) = {z} := by
    apply Set.Subset.antisymm
    · intro t ht
      have H : t ∈ zeroLocus (J : Set D) := by
        change J ≤ t.asIdeal
        exact hz.trans ht
      exact h ▸ H
    · intro t ht
      have htz : t = z := Set.mem_singleton_iff.mp ht
      subst t
      change z.asIdeal ≤ z.asIdeal
      exact le_rfl
  have H := (zeroLocus_eq_iff (I:=J) (J:=z.asIdeal)).mp (h.trans hz'.symm)
  exact hJ.radical.symm.trans (H.trans z.isPrime.isRadical.radical)

/-- Both restrictions are the prime of the same actual lifted point. -/
theorem same_closed_centre [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    [Algebra.EssFiniteType C B] [Algebra.FormallyUnramified C B] (W : Window p r u₀) :
    (first (B:=B) p).map (further W.g) = W.point.asIdeal ∧
      (second (B:=B) r).map (further W.g) = W.point.asIdeal :=
  ⟨ideal_eq_point _ _ (radial_after_away (A:=A) p W.g) W.oldSupport,
    ideal_eq_point _ _ (radial_after_away (A:=C) r W.g) W.splitSupport⟩

end OriginalR47PointedCommonCentre318

#print axioms OriginalR47PointedCommonCentre318.discrete_closed_fibre
#print axioms OriginalR47PointedCommonCentre318.window
#print axioms OriginalR47PointedCommonCentre318.same_closed_centre
