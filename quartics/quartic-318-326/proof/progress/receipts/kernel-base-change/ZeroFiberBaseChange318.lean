module
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace ZeroFiberBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- Exact cartesian family, compatible endomorphisms and sections. No
identification of an endomorphism with multiplication is built into this API. -/
structure Data (E E' B B':Scheme) where
  p:E ⟶ B
  p':E' ⟶ B'
  f:E' ⟶ E
  b:B' ⟶ B
  cartesian:IsPullback f p' p b
  t:E ⟶ E
  t':E' ⟶ E'
  e:B ⟶ E
  e':B' ⟶ E'
  t_base:t ≫ p=p
  t'_base:t' ≫ p'=p'
  e_base:e ≫ p=𝟙 B
  e'_base:e' ≫ p'=𝟙 B'
  commute:f ≫ t=t' ≫ f
  section_map:e' ≫ f=b ≫ e

variable {E E' B B':Scheme} (d:Data E E' B B')
abbrev kernel := pullback d.t d.e
abbrev kernel' := pullback d.t' d.e'
abbrev baseChange := pullback (pullback.snd d.t d.e) d.b

@[reassoc] lemma kernel_base : pullback.fst d.t d.e ≫ d.p=pullback.snd d.t d.e := by
  have h:=congrArg (fun f=>f ≫ d.p) (pullback.condition (f:=d.t) (g:=d.e))
  simpa only [Category.assoc,d.t_base,d.e_base,Category.comp_id] using h
@[reassoc] lemma kernel'_base : pullback.fst d.t' d.e' ≫ d.p'=pullback.snd d.t' d.e' := by
  have h:=congrArg (fun f=>f ≫ d.p') (pullback.condition (f:=d.t') (g:=d.e'))
  simpa only [Category.assoc,d.t'_base,d.e'_base,Category.comp_id] using h

/-- The actual induced map between the actual zero fibers. -/
@[expose] def map : kernel' d ⟶ kernel d :=
  pullback.lift (pullback.fst d.t' d.e' ≫ d.f) (pullback.snd d.t' d.e' ≫ d.b) (by
    rw [Category.assoc,d.commute,←Category.assoc,pullback.condition,Category.assoc,d.section_map,Category.assoc])
@[reassoc] lemma map_fst : map d ≫ pullback.fst d.t d.e=pullback.fst d.t' d.e' ≫ d.f := by simp [map]
@[reassoc] lemma map_snd : map d ≫ pullback.snd d.t d.e=pullback.snd d.t' d.e' ≫ d.b := by simp [map]
@[expose] def toBaseChange : kernel' d ⟶ baseChange d :=
  pullback.lift (map d) (pullback.snd d.t' d.e') (map_snd d)
@[reassoc] lemma toBaseChange_fst : toBaseChange d ≫ pullback.fst _ _=map d := by simp [toBaseChange]
@[reassoc] lemma toBaseChange_snd : toBaseChange d ≫ pullback.snd _ _=pullback.snd d.t' d.e' := by simp [toBaseChange]

@[expose] def point : baseChange d ⟶ E' :=
  d.cartesian.lift (pullback.fst (pullback.snd d.t d.e) d.b ≫ pullback.fst d.t d.e)
    (pullback.snd (pullback.snd d.t d.e) d.b) (by
      rw [Category.assoc,kernel_base]
      exact pullback.condition)
@[reassoc] lemma point_f : point d ≫ d.f=
    pullback.fst (pullback.snd d.t d.e) d.b ≫ pullback.fst d.t d.e := by simp [point]
@[reassoc] lemma point_base : point d ≫ d.p'=pullback.snd (pullback.snd d.t d.e) d.b := by simp [point]
lemma point_condition : point d ≫ d.t'=pullback.snd (pullback.snd d.t d.e) d.b ≫ d.e' := by
  apply d.cartesian.hom_ext
  · rw [Category.assoc,←d.commute,←Category.assoc,point_f,Category.assoc,pullback.condition,
      ←Category.assoc,pullback.condition,Category.assoc,Category.assoc,d.section_map]
  · rw [Category.assoc,d.t'_base,point_base,Category.assoc,d.e'_base,Category.comp_id]
@[expose] def fromBaseChange : baseChange d ⟶ kernel' d :=
  pullback.lift (point d) (pullback.snd (pullback.snd d.t d.e) d.b) (point_condition d)
@[reassoc] lemma fromBaseChange_fst : fromBaseChange d ≫ pullback.fst d.t' d.e'=point d := by simp [fromBaseChange]
@[reassoc] lemma fromBaseChange_snd : fromBaseChange d ≫ pullback.snd d.t' d.e'=
    pullback.snd (pullback.snd d.t d.e) d.b := by simp [fromBaseChange]

lemma toBaseChange_point : toBaseChange d ≫ point d=pullback.fst d.t' d.e' := by
  apply d.cartesian.hom_ext
  · simp only [Category.assoc,point_f,toBaseChange_fst_assoc,map_fst]
  · simp only [Category.assoc,point_base,toBaseChange_snd,kernel'_base]
lemma fromBaseChange_map : fromBaseChange d ≫ map d=pullback.fst (pullback.snd d.t d.e) d.b := by
  apply pullback.hom_ext
  · simp only [Category.assoc,map_fst,fromBaseChange_fst_assoc,point_f]
  · simp only [Category.assoc,map_snd,fromBaseChange_snd_assoc,pullback.condition]

/-- Exact zero fibers commute with the given actual cartesian base change,
with explicit inverse maps and both kernel/base projection identities. -/
@[expose] def iso : kernel' d ≅ baseChange d where
  hom:=toBaseChange d
  inv:=fromBaseChange d
  hom_inv_id:=by
    apply pullback.hom_ext
    · simp only [Category.assoc,fromBaseChange_fst,toBaseChange_point,Category.id_comp]
    · simp only [Category.assoc,fromBaseChange_snd,toBaseChange_snd,Category.id_comp]
  inv_hom_id:=by
    apply pullback.hom_ext
    · simp only [Category.assoc,toBaseChange_fst,fromBaseChange_map,Category.id_comp]
    · simp only [Category.assoc,toBaseChange_snd,fromBaseChange_snd,Category.id_comp]

theorem isPullback : IsPullback (map d) (pullback.snd d.t' d.e') (pullback.snd d.t d.e) d.b :=
  IsPullback.of_iso_pullback ⟨map_snd d⟩ (iso d) (toBaseChange_fst d) (toBaseChange_snd d)
end ZeroFiberBaseChange318
