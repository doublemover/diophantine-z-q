module
public import PullbackBaseIso318
public section
noncomputable section
namespace PullbackOverlapIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Y B U V : Scheme.{u}} (p : Y ⟶ B) (a : U ⟶ B) (b : V ⟶ B)
local notation "A" => pullback p a
local notation "C" => pullback p b
local notation "X" => pullback (pullback.fst p a) (pullback.fst p b)
local notation "T" => pullback a b
local notation "Q" => pullback p (pullback.fst a b ≫ a)

@[expose] def base : X ⟶ T :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd p a)
    (pullback.snd _ _ ≫ pullback.snd p b) (by
      rw [Category.assoc,← pullback.condition,← Category.assoc,
        pullback.condition,Category.assoc,pullback.condition,Category.assoc])
@[reassoc] lemma base_fst : base p a b ≫ pullback.fst a b=
    pullback.fst _ _ ≫ pullback.snd p a := pullback.lift_fst ..
@[reassoc] lemma base_snd : base p a b ≫ pullback.snd a b=
    pullback.snd _ _ ≫ pullback.snd p b := pullback.lift_snd ..

@[expose] def hom : X ⟶ Q :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst p a) (base p a b) (by
    rw [← Category.assoc,base_fst,Category.assoc,pullback.condition,Category.assoc])
@[expose] def left : Q ⟶ A :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst a b) (by
    rw [Category.assoc,pullback.condition])
@[expose] def right : Q ⟶ C :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd a b) (by
    rw [Category.assoc, pullback.condition (f := p) (g := pullback.fst a b ≫ a),
      pullback.condition (f := a) (g := b)])
@[expose] def inv : Q ⟶ X :=
  pullback.lift (left p a b) (right p a b) (by simp only [left,right,pullback.lift_fst])

/-- The actual intersection of two pulled-back chart opens is the
pullback of their ACTUAL base intersection. This identifies full
schemes and both overlap legs, rather than their underlying point sets. -/
@[expose] def iso : X ≅ Q where
  hom := hom p a b
  inv := inv p a b
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [hom,inv,left,Category.assoc,pullback.lift_fst,Category.id_comp]
      · simp only [hom,inv,left,Category.assoc,pullback.lift_fst,pullback.lift_snd,
          pullback.lift_snd_assoc,base_fst,Category.id_comp]
    · apply pullback.hom_ext
      · simp only [hom,inv,right,Category.assoc,pullback.lift_fst,pullback.lift_snd,
          Category.id_comp]
        exact pullback.condition
      · simp only [hom,inv,right,Category.assoc,pullback.lift_fst,pullback.lift_snd,
          pullback.lift_snd_assoc,base_snd,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [hom,inv,left,Category.assoc,pullback.lift_fst,pullback.lift_fst_assoc,
        Category.id_comp]
    · apply pullback.hom_ext
      · simp only [hom,inv,left,Category.assoc,pullback.lift_fst,pullback.lift_snd,
          pullback.lift_snd_assoc,base_fst,Category.id_comp]
      · simp only [hom,inv,right,Category.assoc,pullback.lift_fst,pullback.lift_snd,
          pullback.lift_snd_assoc,base_snd,Category.id_comp]
@[reassoc] lemma hom_original : (iso p a b).hom ≫ pullback.fst p (pullback.fst a b ≫ a)=
    pullback.fst _ _ ≫ pullback.fst p a := pullback.lift_fst ..
@[reassoc] lemma hom_first : (iso p a b).hom ≫ pullback.snd _ _ ≫ pullback.fst a b=
    pullback.fst _ _ ≫ pullback.snd p a := by
  change hom p a b ≫ pullback.snd _ _ ≫ pullback.fst a b=_
  rw [hom,pullback.lift_snd_assoc,base_fst]
@[reassoc] lemma hom_second : (iso p a b).hom ≫ pullback.snd _ _ ≫ pullback.snd a b=
    pullback.snd _ _ ≫ pullback.snd p b := by
  change hom p a b ≫ pullback.snd _ _ ≫ pullback.snd a b=_
  rw [hom,pullback.lift_snd_assoc,base_snd]
end PullbackOverlapIntersection318
