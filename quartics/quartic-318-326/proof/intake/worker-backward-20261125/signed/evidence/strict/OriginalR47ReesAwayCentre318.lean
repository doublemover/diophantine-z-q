module
public import OriginalR47ReesProjFlat318
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.Flat.Localization
public section
noncomputable section

namespace OriginalR47ReesAwayCentre318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318
open OriginalAffineReesChartLocal318 OriginalReesDegreeOneCover318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

abbrev topChart : Type u := chart (⊤ : Ideal A) 1 (Submodule.mem_top)

theorem top_scalars_bijective :
    Function.Bijective (chartScalars (⊤ : Ideal A) 1 Submodule.mem_top) := by
  let p := chartScalars (⊤ : Ideal A) 1 Submodule.mem_top
  constructor
  · intro x y h
    have h₁ := congrArg (chartEval (⊤ : Ideal A) 1 Submodule.mem_top) h
    rw [chartEval_scalar (⊤ : Ideal A) 1 Submodule.mem_top x,
      chartEval_scalar (⊤ : Ideal A) 1 Submodule.mem_top y] at h₁
    have hUnits : Submonoid.powers (1 : A) ≤ nonZeroDivisors A := by
      rintro _ ⟨n,rfl⟩
      change (1 : A)^n ∈ nonZeroDivisors A
      rw [one_pow]
      exact one_mem _
    exact IsLocalization.injective (Localization.Away (1 : A)) hUnits h₁
  · intro z
    obtain ⟨n,b,hb⟩ := clear (⊤ : Ideal A) 1 Submodule.mem_top z
    refine ⟨b,?_⟩
    change z * p (1:A)^n = p b at hb
    change p b = z
    have hn : (1 : A)^n = 1 := one_pow n
    have hOne : p (1 : A) = (1 : @topChart A _) := p.map_one
    calc
      p b = z * (p (1 : A))^n := hb.symm
      _ = z * p ((1 : A)^n) :=
        congrArg (fun c : @topChart A _ => z * c) ((p.map_pow (1 : A) n).symm)
      _ = z * p (1 : A) := congrArg (fun a : A => z * p a) hn
      _ = z * (1 : @topChart A _) := congrArg (fun c : @topChart A _ => z * c) hOne
      _ = z := mul_one z

theorem top_chart_iso : IsIso (chartMap (⊤ : Ideal A) 1 Submodule.mem_top) := by
  let a : Unit → (⊤ : Ideal A) := fun _ => ⟨1,Submodule.mem_top⟩
  have hs : Ideal.span (Set.range fun i => (a i).val) = (⊤ : Ideal A) := by
    change Ideal.span (Set.range (fun _ : Unit => (1 : A))) = ⊤
    rw [Set.range_const, Ideal.span_singleton_one]
  let C := Proj.affineOpenCoverOfIrrelevantLESpan (grade (⊤ : Ideal A))
    (m := fun _ => 1) (gens ⊤ Unit a) (fun i => generator_grade _ _ (a i).property)
    (fun _ => show 0 < (1:ℕ) by decide) (span_covers ⊤ a hs)
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  constructor
  · change IsOpenImmersion (Proj.awayι _ _ _ _)
    infer_instance
  · constructor
    intro x
    obtain ⟨⟨⟩,y,hy⟩ := C.openCover.exists_eq x
    exact ⟨y,hy⟩

/-- Blowing up the unit ideal on the true Rees Proj is the identity. -/
theorem top_projection_iso : IsIso (projection (⊤ : Ideal A)) := by
  let p := chartScalars (⊤ : Ideal A) 1 Submodule.mem_top
  let e := (RingEquiv.ofBijective p top_scalars_bijective).toCommRingCatIso
  let hChart : IsIso (chartMap (⊤ : Ideal A) 1 Submodule.mem_top) := top_chart_iso
  have he : chartMap (⊤ : Ideal A) 1 Submodule.mem_top ≫ projection (⊤ : Ideal A) =
      Spec.map e.hom := chart_over (⊤ : Ideal A) 1 Submodule.mem_top
  have H : projection (⊤ : Ideal A) =
      inv (chartMap (⊤ : Ideal A) 1 Submodule.mem_top) ≫ Spec.map e.hom := by
    rw [← he, IsIso.inv_hom_id_assoc]
  rw [H]
  infer_instance

variable (I : Ideal A) {ι : Type u} (a : ι → I)
variable (hspan : Ideal.span (Set.range (fun i => (a i).val)) = I)

include hspan in
/-- On D(g) with g in the actual centre ideal, the exact inverse image
of the whole Proj round is the same original D(g), not just bijective
on points or the generic fibre. -/
theorem basic_open (g : A) (hg : g ∈ I) :
    ∃ k : Spec (CommRingCat.of (Localization.Away g)) ⟶ blowup I,
      IsPullback k (𝟙 _) (projection I)
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g)))) := by
  let B := Localization.Away g
  let f := algebraMap A B
  let hFlat : Module.Flat A B := IsLocalization.flat B (Submonoid.powers g)
  have ht : I.map f = ⊤ := Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem f hg) (IsLocalization.Away.algebraMap_isUnit g)
  let hProj : IsIso (projection (I.map f)) := ht.symm ▸ top_projection_iso
  let e := asIso (projection (I.map f))
  let F := OriginalR47ReesProjFlat318.projMap (B:=B) I a hspan
  have hs : IsPullback F (projection (I.map f)) (projection I)
      (Spec.map (CommRingCat.ofHom f)) :=
    OriginalR47ReesProjFlat318.cartesian (B:=B) I a hspan
  refine ⟨e.inv ≫ F, hs.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_⟩
  · change F ≫ 𝟙 _ = e.hom ≫ e.inv ≫ F
    simp only [Category.comp_id,e.hom_inv_id_assoc]
  · change e.hom ≫ 𝟙 _ = e.hom ≫ 𝟙 _
    rfl
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
  · change Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A B))
    rfl

end OriginalR47ReesAwayCentre318

#print axioms OriginalR47ReesAwayCentre318.top_projection_iso
#print axioms OriginalR47ReesAwayCentre318.basic_open
