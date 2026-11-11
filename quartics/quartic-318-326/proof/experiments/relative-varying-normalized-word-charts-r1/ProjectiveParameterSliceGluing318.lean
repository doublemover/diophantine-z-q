module
public import ProjectiveParameterSliceTripleSchemes318
public section
noncomputable section
namespace ProjectiveParameterSliceGluing318
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

variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "inc" => ProjectiveParameterSliceSchemes318.inclusion R P
local notation "e" => ProjectiveParameterSliceTriplePullback318.comparison R P
local notation "rot" => ProjectiveParameterSliceTripleSchemes318.rotation R P

@[expose] def tripleTransition (i j k : Fin F.size) :
    pullback (inc i j) (inc i k) ⟶ pullback (inc j k) (inc j i) :=
  (e i j k).inv ≫ rot i j k ≫ (e j k i).hom

lemma triple_leg (i j k : Fin F.size) :
    tripleTransition R P i j k ≫ pullback.snd _ _=pullback.fst _ _ ≫
      (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom :=
  conjugate_leg (e i j k) (e j k i) (rot i j k)
    (ProjectiveParameterSliceTriplePullback318.first R P i j k)
    (ProjectiveParameterSliceTriplePullback318.second R P j k i)
    (pullback.fst _ _) (pullback.snd _ _)
    (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom
    (ProjectiveParameterSliceTriplePullback318.comparison_fst R P i j k)
    (ProjectiveParameterSliceTriplePullback318.comparison_snd R P j k i)
    (ProjectiveParameterSliceTripleSchemes318.leg R P i j k)
lemma triple_cycle (i j k : Fin F.size) :
    tripleTransition R P i j k ≫ tripleTransition R P j k i ≫ tripleTransition R P k i j=𝟙 _ :=
  conjugate_cycle (e i j k) (e j k i) (e k i j) (rot i j k) (rot j k i) (rot k i j)
    (ProjectiveParameterSliceTripleSchemes318.cycle R P i j k)

/-- Full genuine scheme gluing data for the original finite-projective
section parameter quotient charts. The triple maps use the ACTUAL
pullbacks and satisfy the ACTUAL categorical cocycle. -/
@[expose] def data : Scheme.GlueData where
  J := Fin F.size
  U := ProjectiveParameterSliceSchemes318.chart R P
  V := fun ij => ProjectiveParameterSliceSchemes318.overlap R P ij.1 ij.2
  f := inc
  f_id := fun i => ProjectiveParameterSliceSelf318.self_inclusion R P i
  t := fun i j => (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom
  t_id := ProjectiveParameterSliceSelf318.transition_self R P
  t' := tripleTransition R P
  t_fac := triple_leg R P
  cocycle := triple_cycle R P
  f_open := fun i j => inferInstance

/-- An ACTUAL scheme glued from the represented affine normalization
slices, not a set of unit orbits. Its global quotient universal property
and descent of the original zero family are separate next steps. -/
abbrev scheme : Scheme := (data R P).glued
abbrev into (i : Fin F.size) : ProjectiveParameterSliceSchemes318.chart R P i ⟶ scheme R P :=
  (data R P).ι i
instance into_open (i : Fin F.size) : IsOpenImmersion (into R P i) := inferInstance
abbrev cover : (scheme R P).OpenCover := (data R P).openCover
lemma jointly_surjective (x : scheme R P) : ∃ i y,into R P i y=x :=
  (data R P).ι_jointly_surjective x

/-- The actual original pairwise maps become equal after gluing. -/
@[reassoc] lemma glue_condition (i j : Fin F.size) :
    (ProjectiveParameterSliceSchemes318.transitionIso R P i j).hom ≫ inc j i ≫ into R P j=
      inc i j ≫ into R P i :=
  (data R P).glue_condition i j
end ProjectiveParameterSliceGluing318
