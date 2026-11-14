module
public import VaryingWordFamilySelf318
public section
noncomputable section
namespace VaryingWordFamilyGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

private lemma conjugate_leg {C : Type*} [Category C] {X Y P Q A B : C}
    (e : X ≅ P) (f : Y ≅ Q) (r : X ⟶ Y) (a : X ⟶ A) (b : Y ⟶ B)
    (p : P ⟶ A) (q : Q ⟶ B) (t : A ⟶ B)
    (hp : e.hom ≫ p=a) (hq : f.hom ≫ q=b) (h : r ≫ b=a ≫ t) :
    (e.inv ≫ r ≫ f.hom) ≫ q=p ≫ t := by
  simp only [Category.assoc,hq,h,← hp,Iso.inv_hom_id_assoc]

private lemma conjugate_cycle {C : Type*} [Category C] {X Y Z P Q W : C}
    (e : X ≅ P) (f : Y ≅ Q) (g : Z ≅ W) (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ X)
    (h : a ≫ b ≫ c=𝟙 X) :
    (e.inv ≫ a ≫ f.hom) ≫ (f.inv ≫ b ≫ g.hom) ≫ (g.inv ≫ c ≫ e.hom)=𝟙 P := by
  calc
    _ = e.inv ≫ (a ≫ b ≫ c) ≫ e.hom := by
      simp only [Category.assoc,Iso.hom_inv_id_assoc]
    _ = 𝟙 P := by rw [h]; simp only [Category.id_comp,Iso.inv_hom_id]

universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
local notation "inc" => VaryingWordOverlapFamily318.into R A ι
local notation "e" => VaryingWordFamilyTriplePullback318.comparison R A ι
local notation "rot" => VaryingWordTripleFamilyMaps318.rotation R A ι

@[expose] def tripleTransition (w v u : ι → List A) :
    pullback (inc w v) (inc w u) ⟶ pullback (inc v u) (inc v w) :=
  (e w v u).inv ≫ rot w v u ≫ (e v u w).hom
lemma triple_leg (w v u : ι → List A) :
    tripleTransition R A ι w v u ≫ pullback.snd _ _=pullback.fst _ _ ≫
      (VaryingWordFamilyTransition318.transition R A ι w v).hom :=
  conjugate_leg (e w v u) (e v u w) (rot w v u)
    (VaryingWordTripleFamilyMaps318.first R A ι w v u)
    (VaryingWordTripleFamilyMaps318.second R A ι v u w)
    (pullback.fst _ _) (pullback.snd _ _)
    ((VaryingWordFamilyTransition318.transition R A ι w v).hom)
    (VaryingWordFamilyTriplePullback318.comparison_fst R A ι w v u)
    (VaryingWordFamilyTriplePullback318.comparison_snd R A ι v u w)
    (VaryingWordFamilyCocycle318.leg R A ι w v u)
lemma triple_cycle (w v u : ι → List A) :
    tripleTransition R A ι w v u ≫ tripleTransition R A ι v u w ≫ tripleTransition R A ι u w v=𝟙 _ :=
  conjugate_cycle (e w v u) (e v u w) (e u w v) (rot w v u) (rot v u w) (rot u w v)
    (VaryingWordFamilyCocycle318.cycle R A ι w v u)

/-- Genuine scheme gluing data for the actual normalized quotient families.
Every triple map is on the actual categorical family intersection. -/
@[expose] def data : Scheme.GlueData where
  J := ι → List A
  U := VaryingNormalizedUniversalFamily318.family R A ι
  V := fun wv => VaryingWordOverlapFamily318.scheme R A ι wv.1 wv.2
  f := inc
  f_id := fun w => VaryingWordFamilySelf318.inclusion_self R A ι w
  t := fun w v => (VaryingWordFamilyTransition318.transition R A ι w v).hom
  t_id := VaryingWordFamilySelf318.transition_self R A ι
  t' := tripleTransition R A ι
  t_fac := triple_leg R A ι
  cocycle := triple_cycle R A ι
  f_open := fun w v => inferInstance

/-- The actual quotient-family scheme glued from its finite-flat chart
families. Projection descent and global classification are separate statements. -/
abbrev scheme : Scheme := (data R A ι).glued
abbrev into (w : ι → List A) : VaryingNormalizedUniversalFamily318.family R A ι w ⟶ scheme R A ι :=
  (data R A ι).ι w
instance into_open (w : ι → List A) : IsOpenImmersion (into R A ι w) := inferInstance
abbrev cover : (scheme R A ι).OpenCover := (data R A ι).openCover
lemma jointly_surjective (x : scheme R A ι) : ∃ w y,into R A ι w y=x :=
  (data R A ι).ι_jointly_surjective x
@[reassoc] lemma glue_condition (w v : ι → List A) :
    (VaryingWordFamilyTransition318.transition R A ι w v).hom ≫ inc v w ≫ into R A ι v=
      inc w v ≫ into R A ι w :=
  (data R A ι).glue_condition w v
end VaryingWordFamilyGluing318
