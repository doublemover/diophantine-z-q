module
public import OriginalR47ReesAffinePushout318
public import OriginalReesDegreeOneCover318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public section
noncomputable section

namespace OriginalR47ReesProjFlat318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318
open OriginalReesDegreeOneCover318 (gens span_covers)
open OriginalR47ReesCoefficientMap318 (mapGraded generator_read)
open OriginalR47ReesChartMapValues318 (chartHom newHa)
open HomogeneousLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)
variable {ι : Type u} (a : ι → I)
variable (hspan : Ideal.span (Set.range (fun i => (a i).val)) = I)
local notation "f" => algebraMap A B

abbrev mapped (i : ι) : I.map f :=
  ⟨f (a i).val, Ideal.mem_map_of_mem f (a i).property⟩

include hspan in
theorem mapped_span :
    Ideal.span (Set.range (fun i => (mapped (B:=B) I a i).val)) = I.map f := by
  have h : Set.range (fun i => (mapped (B:=B) I a i).val) =
      f '' Set.range (fun i => (a i).val) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨(a i).val, ⟨i,rfl⟩, rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
  rw [h, ← Ideal.map_span, hspan]

include hspan in
/-- The true Proj morphism is defined since old chosen generators
generate the mapped irrelevant ideal after base change. -/
theorem irrelevant :
    HomogeneousIdeal.irrelevant (grade (I.map f)) ≤
      (HomogeneousIdeal.irrelevant (grade I)).map (mapGraded I f) := by
  change (HomogeneousIdeal.irrelevant (grade (I.map f))).toIdeal ≤
    ((HomogeneousIdeal.irrelevant (grade I)).map (mapGraded I f)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  refine (span_covers (I.map f) (mapped (B:=B) I a) (mapped_span I a hspan)).trans
    (Ideal.span_le.mpr ?_)
  rintro _ ⟨i,rfl⟩
  change generator (I.map f) (f (a i).val) (Ideal.mem_map_of_mem f (a i).property) ∈ _
  rw [← generator_read I f (a i).val (a i).property]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ (show 0 < (1:ℕ) by decide)
      (generator_grade I (a i).val (a i).property))

/-- The morphism of the original affine Rees blowups, induced by their
actual graded rings. No isomorphism to a replacement X is assumed. -/
@[expose] def projMap : blowup (I.map f) ⟶ blowup I :=
  Proj.map (mapGraded I f) (irrelevant I a hspan)

private theorem mapped_powers (x : A) (hx : x ∈ I)
    (y : Rees (I.map f)) (hy : mapGraded I f (generator I x hx) = y) :
    Submonoid.powers (generator I x hx) ≤ (Submonoid.powers y).comap (mapGraded I f) := by
  rintro _ ⟨n,rfl⟩
  exact ⟨n, (congrArg (fun z : Rees (I.map f) => z^n) hy).symm.trans
    ((mapGraded I f).map_pow _ n).symm⟩

private theorem named_chart (x : A) (hx : x ∈ I)
    (y : Rees (I.map f)) (hy : mapGraded I f (generator I x hx) = y)
    (hdeg : y ∈ grade (I.map f) 1) :
    (Proj.awayι (grade (I.map f)) y hdeg (by decide)) ≫ projMap I a hspan =
      Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.map (mapGraded I f) (mapped_powers I x hx y hy) :
          chart I x hx →+* Away (grade (I.map f)) y)) ≫
        OriginalAffineReesBlowup318.chartMap I x hx := by
  subst y
  exact Proj.awayι_comp_map (mapGraded I f) (irrelevant I a hspan)
    (show 0 < (1:ℕ) by decide) _ (generator_grade I x hx)

theorem chart_comm (x : A) (hx : x ∈ I) :
    OriginalAffineReesBlowup318.chartMap (I.map f) (f x) (newHa I f x hx) ≫ projMap I a hspan =
      Spec.map (CommRingCat.ofHom (chartHom I f x hx)) ≫
        OriginalAffineReesBlowup318.chartMap I x hx := by
  exact named_chart (B:=B) I a hspan x hx _ (generator_read I f x hx) (generator_grade _ _ _)

theorem chart_open (x : A) (hx : x ∈ I) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (chartHom I f x hx)))
      (OriginalAffineReesBlowup318.chartMap (I.map f) (f x) (newHa I f x hx))
      (OriginalAffineReesBlowup318.chartMap I x hx) (projMap I a hspan) := by
  let : IsOpenImmersion (OriginalAffineReesBlowup318.chartMap I x hx) := by
    change IsOpenImmersion (Proj.awayι (grade I) (generator I x hx)
      (generator_grade I x hx) (by decide : 0 < (1:ℕ)))
    infer_instance
  let : IsOpenImmersion (OriginalAffineReesBlowup318.chartMap (I.map f) (f x)
      (newHa I f x hx)) := by
    change IsOpenImmersion (Proj.awayι (grade (I.map f))
      (generator (I.map f) (f x) (newHa I f x hx))
      (generator_grade (I.map f) (f x) (newHa I f x hx)) (by decide : 0 < (1:ℕ)))
    infer_instance
  apply IsOpenImmersion.isPullback
  · exact chart_comm (B:=B) I a hspan x hx
  · simp only [OriginalAffineReesBlowup318.chartMap, Proj.opensRange_awayι,
      projMap, Proj.map_preimage_basicOpen, generator_read]

abbrev oldCover : (blowup I).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grade I) (m := fun _ => 1) (gens I ι a)
    (fun i => generator_grade I (a i).val (a i).property)
    (fun _ => show 0 < (1:ℕ) by decide) (span_covers I a hspan)

/-- On the given old cover, the preimage under the genuine Proj morphism
is the actual B chart, and over the base this is the affine tensor square. -/
theorem cartesian [Module.Flat A B] :
    IsPullback (projMap I a hspan) (projection (I.map f)) (projection I)
      (Spec.map (CommRingCat.ofHom f)) := by
  let U := (oldCover I a hspan).openCover
  apply Scheme.isPullback_of_openCover _ _ _ _ U
  intro i
  let x : A := (a i).val
  let hx : x ∈ I := (a i).property
  have hOpen := (chart_open (B:=B) I a hspan x hx).flip
  let e := hOpen.isoPullback
  have h := (OriginalR47ReesAffinePushout318.affine_pullback (B:=B) I x hx).flip
  rw [← chart_over I x hx, ← chart_over (I.map f) (f x) (newHa I f x hx)] at h
  apply h.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change Spec.map (CommRingCat.ofHom (chartHom I f x hx)) ≫ 𝟙 _ =
      e.hom ≫ pullback.snd (projMap I a hspan) (OriginalAffineReesBlowup318.chartMap I x hx)
    simpa only [Category.comp_id] using hOpen.isoPullback_hom_snd.symm
  · change (OriginalAffineReesBlowup318.chartMap (I.map f) (f x) (newHa I f x hx) ≫
        projection (I.map f)) ≫ 𝟙 _ =
      e.hom ≫ pullback.fst (projMap I a hspan)
        (OriginalAffineReesBlowup318.chartMap I x hx) ≫ projection (I.map f)
    simpa only [Category.comp_id] using
      (hOpen.isoPullback_hom_fst_assoc (projection (I.map f))).symm
  · change (OriginalAffineReesBlowup318.chartMap I x hx ≫ projection I) ≫ 𝟙 _ =
      𝟙 _ ≫ (OriginalAffineReesBlowup318.chartMap I x hx ≫ projection I)
    simp only [Category.comp_id, Category.id_comp]
  · change Spec.map (CommRingCat.ofHom f) ≫ 𝟙 _ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom f)
    simp only [Category.comp_id, Category.id_comp]

end OriginalR47ReesProjFlat318

#print axioms OriginalR47ReesProjFlat318.irrelevant
#print axioms OriginalR47ReesProjFlat318.chart_comm
#print axioms OriginalR47ReesProjFlat318.chart_open
#print axioms OriginalR47ReesProjFlat318.cartesian
