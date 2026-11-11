module
public import MonoFactorPullback318
public section
noncomputable section
namespace MonoFamilyGlueData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} {J : Type u} (Z : J → Scheme.{u}) (f : ∀ i, Z i ⟶ X)
  [∀ i, Mono (f i)] [∀ i j, IsOpenImmersion (pullback.fst (f i) (f j))]
/-- Actual categorical triple rotation for monomorphic families in one
fixed ambient scheme. No chosen triple-overlap model is substituted. -/
@[expose] def triple (i j k : J) :
    pullback (pullback.fst (f i) (f j)) (pullback.fst (f i) (f k)) ⟶
      pullback (pullback.fst (f j) (f k)) (pullback.fst (f j) (f i)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp
@[reassoc] lemma triple_first_first (i j k : J) : triple Z f i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _=
    pullback.fst _ _ ≫ pullback.snd _ _ := by delta triple; simp
@[reassoc] lemma triple_first_second (i j k : J) : triple Z f i j k ≫ pullback.fst _ _ ≫ pullback.snd _ _=
    pullback.snd _ _ ≫ pullback.snd _ _ := by delta triple; simp
@[reassoc] lemma triple_second_first (i j k : J) : triple Z f i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _=
    pullback.fst _ _ ≫ pullback.snd _ _ := by delta triple; simp
@[reassoc] lemma triple_second_second (i j k : J) : triple Z f i j k ≫ pullback.snd _ _ ≫ pullback.snd _ _=
    pullback.fst _ _ ≫ pullback.fst _ _ := by delta triple; simp
lemma triple_leg (i j k : J) : triple Z f i j k ≫ pullback.snd _ _=
    pullback.fst _ _ ≫ (pullbackSymmetry (f i) (f j)).hom := by
  apply pullback.hom_ext <;> simp only [Category.assoc,triple_second_first,triple_second_second,
    pullbackSymmetry_hom_comp_fst,pullbackSymmetry_hom_comp_snd]
lemma triple_cycle (i j k : J) : triple Z f i j k ≫ triple Z f j k i ≫ triple Z f k i j=𝟙 _ := by
  apply pullback.hom_ext <;> apply pullback.hom_ext <;>
    simp [Category.assoc,triple_first_first,triple_first_second,
      triple_second_first,triple_second_second,pullback.condition]
/-- The overlap schemes are the TRUE ambient fiber products of the
actual local families; their rotation and cocycle are categorical. -/
@[expose] def data : Scheme.GlueData where
  J := J
  U := Z
  V := fun ij => pullback (f ij.1) (f ij.2)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id _ := by simp
  t' := triple Z f
  t_fac := triple_leg Z f
  cocycle := triple_cycle Z f
  f_open _ _ := inferInstance
abbrev scheme : Scheme := (data Z f).glued
abbrev into (i : J) : Z i ⟶ scheme Z f := (data Z f).ι i
abbrev cover : (scheme Z f).OpenCover := (data Z f).openCover
@[expose] def map : scheme Z f ⟶ X := by
  fapply Multicoequalizer.desc
  · exact f
  rintro ⟨i,j⟩
  simp only [Category.assoc,pullbackSymmetry_hom_comp_fst_assoc]
  exact pullback.condition
@[reassoc] lemma into_map (i : J) : into Z f i ≫ map Z f=f i := Multicoequalizer.π_desc _ _ _ _ _
lemma intersection (i j : J) : IsPullback (pullback.fst (f i) (f j))
    (pullback.snd (f i) (f j)) (into Z f i) (into Z f j) := by
  have h := IsPullback.of_isLimit ((data Z f).vPullbackConeIsLimit i j)
  simpa only [data,pullbackSymmetry_hom_comp_fst] using h
end MonoFamilyGlueData318
