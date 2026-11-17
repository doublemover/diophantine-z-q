module
public import RankOneAffineColumnCover318
public import RankOneProjectiveColumns318
public import ReducedComplexPointMorphisms318
public section
noncomputable section
namespace RankOneAffineProjectiveMorphism318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RankOneAffineColumnCover318
variable {ι κ A : Type*} [Finite ι] [CommRing A] [Algebra ℂ A]
  [Algebra.FiniteType ℂ A] [_root_.IsReduced A]
variable (w : ι → κ → A)
local instance standardGrading : GradedAlgebra (ComplexProjectiveMarkerPoint318.grading (ι := ι)) :=
  MvPolynomial.gradedAlgebra
local instance sourceFiniteType : LocallyOfFiniteType
    (AffineComplexProjectiveVector318.structureMap (A := A)) := by
  dsimp [AffineComplexProjectiveVector318.structureMap]
  infer_instance

theorem compatible (hw : ∀ i j s t, w i s*w j t=w i t*w j s) (rs st : ι × κ) :
    pullback.fst (entryMap w rs) (entryMap w st)≫localMap w rs=
      pullback.snd (entryMap w rs) (entryMap w st)≫localMap w st := by
  let a := entryMap w rs
  let b := entryMap w st
  let π := (pullback.fst a b≫a)≫AffineComplexProjectiveVector318.structureMap (A := A)
  letI : IsReduced (pullback a b) := isReduced_of_isOpenImmersion (pullback.fst a b≫a)
  letI : LocallyOfFiniteType π := by dsimp [π,a,b]; infer_instance
  have hj : (pullback.fst a b≫localMap w rs)≫ComplexProjectiveBase318.structureMap=π := by
    rw [Category.assoc]
    change pullback.fst a b≫(AffineComplexProjectiveVector318.morphism _ _≫
      ComplexProjectiveBase318.structureMap)=_
    rw [AffineComplexProjectiveVector318.over_complex]
    dsimp [π,a]
    rw [Category.assoc,entry_base]
  have hk : (pullback.snd a b≫localMap w st)≫ComplexProjectiveBase318.structureMap=π := by
    rw [Category.assoc]
    change pullback.snd a b≫(AffineComplexProjectiveVector318.morphism _ _≫
      ComplexProjectiveBase318.structureMap)=_
    rw [AffineComplexProjectiveVector318.over_complex,←entry_base w st,←Category.assoc]
    exact congrArg (fun h => h≫AffineComplexProjectiveVector318.structureMap (A := A))
      (pullback.condition (f := a) (g := b)).symm
  apply ReducedComplexPointMorphisms318.ext π ComplexProjectiveBase318.structureMap _ _ hj hk
  intro p hp
  have hpj : (p≫pullback.fst a b)≫
      AffineComplexProjectiveVector318.structureMap (A := EntryRing w rs)=𝟙 _ := by
    rw [←entry_base,Category.assoc,←Category.assoc (pullback.fst a b)]
    exact hp
  have hpk : (p≫pullback.snd a b)≫
      AffineComplexProjectiveVector318.structureMap (A := EntryRing w st)=𝟙 _ := by
    rw [←entry_base,Category.assoc,←Category.assoc (pullback.snd a b),←pullback.condition]
    exact hp
  obtain ⟨f,hf⟩ := AffineComplexProjectiveVector318.exists_algebraPoint
    (p≫pullback.fst a b) hpj
  obtain ⟨g,hg⟩ := AffineComplexProjectiveVector318.exists_algebraPoint
    (p≫pullback.snd a b) hpk
  have hbase : baseEvaluation w rs f=baseEvaluation w st g := by
    have hs : Spec.map (CommRingCat.ofHom (baseEvaluation w rs f).toRingHom)=
        Spec.map (CommRingCat.ofHom (baseEvaluation w st g).toRingHom) := by
      rw [←base_point,←base_point,←hf,←hg]
      simp only [Category.assoc,pullback.condition_assoc]
    have he := Spec.map_injective hs
    ext x
    exact congrArg (fun h => h.hom x) he
  have hrank : ∀ i j s t,
      baseEvaluation w rs f (w i s)*baseEvaluation w rs f (w j t)=
        baseEvaluation w rs f (w i t)*baseEvaluation w rs f (w j s) := by
    intro i j s t
    simpa only [map_mul] using congrArg (baseEvaluation w rs f) (hw i j s t)
  have hst : ∃ i,baseEvaluation w rs f (w i st.2)≠0 := by
    rw [hbase]
    exact ⟨st.1,base_nonzero w st g⟩
  have he := RankOneProjectiveColumns318.scheme_columns
    (fun i s => baseEvaluation w rs f (w i s)) hrank rs.2 st.2
    ⟨rs.1,base_nonzero w rs f⟩ hst
  rw [←Category.assoc,←Category.assoc,hf,hg,local_point_action,local_point_action]
  simpa only [hbase] using he

/-- A rank-one unit-ideal matrix over the ACTUAL reduced finite-type
complex algebra gives a genuine projective morphism. Each column is
used only where a specified entry is invertible; all these actual
principal opens are glued, so no zero column is divided out. -/
@[expose] def morphism
    (hspan : Ideal.span (Set.range (fun rs : ι × κ => w rs.1 rs.2))=⊤)
    (hw : ∀ i j s t, w i s*w j t=w i t*w j s) :
    Spec (CommRingCat.of A) ⟶ Proj (ComplexProjectiveMarkerPoint318.grading (ι := ι)) :=
  (cover w hspan).glueMorphisms (localMap w) (compatible w hw)

@[reassoc] theorem entry_morphism
    (hspan : Ideal.span (Set.range (fun rs : ι × κ => w rs.1 rs.2))=⊤)
    (hw : ∀ i j s t, w i s*w j t=w i t*w j s) (rs : ι × κ) :
    entryMap w rs≫morphism w hspan hw=localMap w rs :=
  (cover w hspan).ι_glueMorphisms _ _ rs

@[reassoc] theorem over_complex
    (hspan : Ideal.span (Set.range (fun rs : ι × κ => w rs.1 rs.2))=⊤)
    (hw : ∀ i j s t, w i s*w j t=w i t*w j s) :
    morphism w hspan hw≫ComplexProjectiveBase318.structureMap=
      AffineComplexProjectiveVector318.structureMap (A := A) := by
  apply (cover w hspan).hom_ext
  intro rs
  rw [←Category.assoc,entry_morphism]
  exact (AffineComplexProjectiveVector318.over_complex _ _).trans (entry_base w rs).symm
end RankOneAffineProjectiveMorphism318
