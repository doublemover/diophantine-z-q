module
public import OriginalR47ReesAwayCentre318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section

namespace OriginalR47ReesCentreFreeProjection318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PrimeSpectrum
open OriginalAffineReesBlowup318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A] (I : Ideal A)

abbrev old := Spec (CommRingCat.of A)

def off : (old (A:=A)).Opens :=
  ⟨(zeroLocus (I : Set A))ᶜ, (isClosed_zeroLocus _).isOpen_compl⟩

abbrev bMap (z : I) : Spec (CommRingCat.of (Localization.Away z.val)) ⟶ old (A:=A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away z.val)))

theorem bMap_range (z : I) : Set.range (bMap I z) ⊆ Set.range (off I).ι := by
  rw [Scheme.Opens.range_ι]
  change Set.range (comap (algebraMap A (Localization.Away z.val))) ⊆
    (zeroLocus (I : Set A))ᶜ
  rw [localization_away_comap_range (Localization.Away z.val) z.val]
  intro p hp hI
  change z.val ∉ p.asIdeal at hp
  exact hp (hI z.property)

/-- The real principal open inside the *same* old centre-free open. -/
@[expose] def intoOff (z : I) :
    Spec (CommRingCat.of (Localization.Away z.val)) ⟶ (off I).toScheme :=
  IsOpenImmersion.lift (off I).ι (bMap I z) (bMap_range I z)

@[reassoc (attr := simp)] theorem intoOff_read (z : I) :
    intoOff I z ≫ (off I).ι = bMap I z :=
  IsOpenImmersion.lift_fac _ _ _

instance intoOff_open (z : I) : IsOpenImmersion (intoOff I z) := by
  unfold intoOff
  infer_instance

/-- Each genuine point off the centre belongs to D(g) for some actual
g in its centre ideal. This open cover contains no exceptional point. -/
@[expose] def offCover : (off I).toScheme.OpenCover where
  I₀ := I
  X z := Spec (CommRingCat.of (Localization.Away z.val))
  f := intoOff I
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun t => ?_, fun z => inferInstance⟩
    let x := (off I).ι t
    have hx : x ∈ (off I : Set (old (A:=A))) := by
      rw [← Scheme.Opens.range_ι]; exact Set.mem_range_self t
    change ¬ (I : Set A) ⊆ x.asIdeal at hx
    obtain ⟨g,hg,hxg⟩ := Set.not_subset.mp hx
    let z : I := ⟨g,hg⟩
    have H : x ∈ Set.range (bMap I z) := by
      let p : PrimeSpectrum A := x
      have hmem : p ∈ Set.range (comap (algebraMap A (Localization.Away g))) := by
        rw [localization_away_comap_range (Localization.Away g) g]
        change g ∉ p.asIdeal
        exact hxg
      exact hmem
    obtain ⟨w,hw⟩ := H
    refine ⟨z,w,?_⟩
    apply (off I).ι.isOpenEmbedding.injective
    change (off I).ι (intoOff I z w) = x
    rw [← Scheme.Hom.comp_apply,intoOff_read]
    exact hw

variable {ι : Type u} (a : ι → I)
variable (hspan : Ideal.span (Set.range (fun i => (a i).val)) = I)

include hspan in
private theorem base_snd_iso (z : I) :
    IsIso (pullback.snd (projection I) (bMap I z)) := by
  obtain ⟨k,hk⟩ := OriginalR47ReesAwayCentre318.basic_open I a hspan z.val z.property
  have h : pullback.snd (projection I) (bMap I z) = hk.isoPullback.inv := by
    apply (cancel_epi hk.isoPullback.hom).mp
    rw [hk.isoPullback_hom_snd,hk.isoPullback.hom_inv_id]
  rw [h]
  infer_instance

include hspan in
/-- The whole inverse image of the old centre-free open, by literal
Cartesian restriction of the actual Proj, is that same open. -/
theorem off_iso : IsIso (pullback.snd (projection I) (off I).ι) := by
  let f := pullback.snd (projection I) (off I).ι
  apply IsZariskiLocalAtTarget.of_openCover
    (P := MorphismProperty.isomorphisms Scheme) (offCover I)
  intro z
  change IsIso (pullback.snd f (intoOff I z))
  have h := (IsPullback.of_hasPullback f (intoOff I z)).paste_horiz
     (IsPullback.of_hasPullback (projection I) (off I).ι)
  rw [intoOff_read] at h
  let : IsIso (pullback.snd (projection I) (bMap I z)) := base_snd_iso I a hspan z
  rw [← h.isoPullback_hom_snd]
  infer_instance

theorem off_maximal (p : PrimeSpectrum A) [p.asIdeal.IsMaximal] :
    (off p.asIdeal : Set (old (A:=A))) = {p}ᶜ := by
  have he : zeroLocus (p.asIdeal : Set A) = {p} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_singleton_iff.mpr
        (PrimeSpectrum.ext (Ideal.IsMaximal.eq_of_le ‹p.asIdeal.IsMaximal› x.isPrime.ne_top hx)).symm
    · intro h
      have hx : x = p := Set.mem_singleton_iff.mp h
      change p.asIdeal ≤ x.asIdeal
      rw [hx]
  exact congrArg Set.compl he

/-- On a map from any open entirely outside this actual closed point,
the whole pullback is the identity (the target can be non-affine). -/
theorem outside_point (p : PrimeSpectrum A) [p.asIdeal.IsMaximal]
    {T : Scheme.{u}} (g : T ⟶ old (A:=A)) (hg : ∀ t, g t ≠ p) :
    ∃ k : T ⟶ blowup p.asIdeal,
      IsPullback k (𝟙 T) (projection p.asIdeal) g := by
  let f := projection p.asIdeal
  let V := off p.asIdeal
  have hr : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    change Set.range g ⊆ (off p.asIdeal : Set (old (A:=A)))
    rw [off_maximal p]
    rintro _ ⟨t,rfl⟩
    exact hg t
  let j := IsOpenImmersion.lift V.ι g hr
  let m := pullback.snd f V.ι
  have span : Ideal.span (Set.range (fun a : p.asIdeal => a.val)) = p.asIdeal := by
    have he : Set.range (fun a : p.asIdeal => a.val) = (p.asIdeal : Set A) := by
      ext r
      exact ⟨fun ⟨z,hz⟩ => hz ▸ z.property, fun h => ⟨⟨r,h⟩,rfl⟩⟩
    rw [he,Ideal.span_eq]
  let : IsIso m := off_iso p.asIdeal id span
  have L := IsPullback.of_hasPullback m j
  let : IsIso (pullback.snd m j) := L.isIso_snd_of_isIso
  let e := asIso (pullback.snd m j)
  have H := L.paste_horiz (IsPullback.of_hasPullback f V.ι)
  have hc : j ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  rw [hc] at H
  let F := pullback.fst m j ≫ pullback.fst f V.ι
  refine ⟨e.inv ≫ F,
    H.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_⟩
  · change F ≫ 𝟙 _ = e.hom ≫ e.inv ≫ F
    simp only [Category.comp_id,e.hom_inv_id_assoc]
  · change e.hom ≫ 𝟙 _ = e.hom ≫ 𝟙 _
    rfl
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp,f]
  · change g = g
    rfl

end OriginalR47ReesCentreFreeProjection318

#print axioms OriginalR47ReesCentreFreeProjection318.offCover
#print axioms OriginalR47ReesCentreFreeProjection318.off_iso
#print axioms OriginalR47ReesCentreFreeProjection318.outside_point
