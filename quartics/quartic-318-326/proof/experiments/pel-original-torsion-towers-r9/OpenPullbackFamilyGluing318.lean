module
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public section
noncomputable section
namespace OpenPullbackFamilyGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {ι : Type u} (Z : ι → Scheme.{u}) (f : ∀ i,Z i ⟶ X)
  [∀ i,Mono (f i)] [∀ i j,IsOpenImmersion (pullback.fst (f i) (f j))]

/-- The genuine triple-intersection permutation, using only actual
scheme pullbacks. No covering of X or closed-point assertion is assumed. -/
@[expose] def triple (i j k : ι) :
    pullback (pullback.fst (f i) (f j)) (pullback.fst (f i) (f k)) ⟶
      pullback (pullback.fst (f j) (f k)) (pullback.fst (f j) (f i)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom≫?_≫(pullbackSymmetry _ _).hom
  refine ?_≫(pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp
@[simp,reassoc] lemma triple_fst_fst (i j k : ι) :
    triple Z f i j k≫pullback.fst _ _≫pullback.fst _ _=pullback.fst _ _≫pullback.snd _ _ := by
  dsimp [triple]; simp
@[simp,reassoc] lemma triple_fst_snd (i j k : ι) :
    triple Z f i j k≫pullback.fst _ _≫pullback.snd _ _=pullback.snd _ _≫pullback.snd _ _ := by
  dsimp [triple]; simp
@[simp,reassoc] lemma triple_snd_fst (i j k : ι) :
    triple Z f i j k≫pullback.snd _ _≫pullback.fst _ _=pullback.fst _ _≫pullback.snd _ _ := by
  dsimp [triple]; simp
@[simp,reassoc] lemma triple_snd_snd (i j k : ι) :
    triple Z f i j k≫pullback.snd _ _≫pullback.snd _ _=pullback.fst _ _≫pullback.fst _ _ := by
  dsimp [triple]; simp
lemma triple_cocycle (i j k : ι) :
    triple Z f i j k≫triple Z f j k i≫triple Z f k i j=𝟙 _ := by
  apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp [pullback.condition]

/-- Glue actual local schemes along their FULL pairwise pullbacks over
X. The open-immersion hypotheses concern whole schemes, not point sets. -/
@[expose] def glueData : Scheme.GlueData where
  J := ι
  U := Z
  V ij := pullback (f ij.1) (f ij.2)
  f i j := pullback.fst (f i) (f j)
  f_id i := inferInstance
  t i j := (pullbackSymmetry (f i) (f j)).hom
  t_id i := by simp
  t' := triple Z f
  t_fac i j k := by apply pullback.hom_ext <;> simp
  cocycle := triple_cocycle Z f
  f_open i j := inferInstance
abbrev Glued : Scheme := (glueData Z f).glued
abbrev inclusion (i : ι) : Z i ⟶ Glued Z f := (glueData Z f).ι i
@[expose] def into : Glued Z f ⟶ X := by
  fapply Multicoequalizer.desc
  · exact f
  rintro ⟨i,j⟩
  change pullback.fst _ _≫f i=((pullbackSymmetry _ _).hom≫pullback.fst _ _)≫f j
  simpa using! pullback.condition
@[simp,reassoc] lemma inclusion_into (i : ι) : inclusion Z f i≫into Z f=f i :=
  Multicoequalizer.π_desc _ _ _ _ _
lemma covers (x : Glued Z f) : ∃ i,z : Z i,inclusion Z f i z=x :=
  (glueData Z f).ι_jointly_surjective x

/-- No additional identifications arise: the global glued map is
injective on all underlying scheme points. -/
lemma into_injective : Function.Injective (into Z f) := by
  intro x y h
  obtain ⟨i,x,rfl⟩ := covers Z f x
  obtain ⟨j,y,rfl⟩ := covers Z f y
  have he : f i x=f j y := by simpa only [←Scheme.Hom.comp_apply,inclusion_into] using h
  obtain ⟨z,hz,hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f i) (g := f j) x y he
  apply ((glueData Z f).ι_eq_iff i j x y).mpr
  exact ⟨z,hz,by simpa only [pullbackSymmetry_hom_comp_fst,←Scheme.Hom.comp_apply] using hz'⟩
end OpenPullbackFamilyGluing318
