module
public import InfinityBaseChange318
public import WeierstrassGluing318
import all WeierstrassGluing318
public section
noncomputable section
namespace WeierstrassCoefficientMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassOverlap318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
local notation "a" => algebraMap R S

@[expose] def overlapCoefficient (A B:R) : InfinityOverlap A B →ₐ[R] InfinityOverlap (a A) (a B) :=
  IsLocalization.Away.liftAlgHom
    (f := (Algebra.algHom R (Infinity (a A) (a B)) (InfinityOverlap (a A) (a B))).comp
      (InfinityBaseChange318.coefficientMap A B)) (InfinityChart318.z A B) (by
        change IsUnit (algebraMap (Infinity (a A) (a B)) (InfinityOverlap (a A) (a B))
          (InfinityBaseChange318.coefficientMap A B (InfinityChart318.z A B)))
        rw [InfinityBaseChange318.coefficientMap_z]
        exact IsUnit.of_mul_eq_one _ (iz_ii (a A) (a B)))

lemma overlapCoefficient_base (A B:R) (t:Infinity A B) :
    overlapCoefficient (S:=S) A B (algebraMap (Infinity A B) (InfinityOverlap A B) t)=
      algebraMap (Infinity (a A) (a B)) (InfinityOverlap (a A) (a B))
        (InfinityBaseChange318.coefficientMap A B t) := by
  simp [overlapCoefficient,IsLocalization.Away.liftAlgHom,IsLocalization.Away.lift_eq]
  rfl
@[simp] theorem overlapCoefficient_ix (A B:R) : overlapCoefficient (S:=S) A B (ix A B)=ix (a A) (a B) := by
  unfold ix
  rw [overlapCoefficient_base,InfinityBaseChange318.coefficientMap_x]
@[simp] theorem overlapCoefficient_iz (A B:R) : overlapCoefficient (S:=S) A B (iz A B)=iz (a A) (a B) := by
  unfold iz
  rw [overlapCoefficient_base,InfinityBaseChange318.coefficientMap_z]
@[simp] theorem overlapCoefficient_ii (A B:R) : overlapCoefficient (S:=S) A B (ii A B)=ii (a A) (a B) := by
  have h := congrArg (overlapCoefficient (S:=S) A B) (iz_ii A B)
  rw [map_mul,map_one,overlapCoefficient_iz] at h
  calc
    _ = ii (a A) (a B)*(iz (a A) (a B)*overlapCoefficient A B (ii A B)) := by
      rw [←mul_assoc,mul_comm (ii (a A) (a B)),iz_ii,one_mul]
    _ = ii (a A) (a B) := by rw [h,mul_one]

lemma overlap_finite (A B:R) : (overlapCoefficient (S:=S) A B).comp (toInfinityBase A B)=
    ((toInfinityBase (a A) (a B)).restrictScalars R).comp (AffineBaseChange318.coefficientMap A B) := by
  apply WeierstrassOverlap318.affine_hom_ext
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,toInfinityBase_x,map_mul,
      overlapCoefficient_ix,overlapCoefficient_ii,AffineBaseChange318.coefficientMap_x]
  · simp only [AlgHom.comp_apply,AlgHom.restrictScalars_apply,toInfinityBase_y,
      overlapCoefficient_ii,AffineBaseChange318.coefficientMap_y]

@[expose] def finiteMap (A B:R) : ShortAffineScheme318.scheme (a A) (a B) ⟶ ShortAffineScheme318.scheme A B :=
  Spec.map (CommRingCat.ofHom (AffineBaseChange318.coefficientMap (S:=S) A B).toRingHom)
@[expose] def infinityMap (A B:R) : InfinitySmooth318.scheme (a A) (a B) ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom (InfinityBaseChange318.coefficientMap (S:=S) A B).toRingHom)
@[expose] def overlapMap (A B:R) : WeierstrassGluing318.overlap (a A) (a B) ⟶ WeierstrassGluing318.overlap A B :=
  Spec.map (CommRingCat.ofHom (overlapCoefficient (S:=S) A B).toRingHom)

lemma overlap_finite_map (A B:R) : WeierstrassGluing318.intoAffine (a A) (a B) ≫ finiteMap A B=
    overlapMap A B ≫ WeierstrassGluing318.intoAffine A B := by
  rw [WeierstrassGluing318.intoAffine_eq,WeierstrassGluing318.intoAffine_eq]
  unfold finiteMap overlapMap
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (overlap_finite A B)).symm
lemma overlap_infinity_map (A B:R) : WeierstrassGluing318.intoInfinity (a A) (a B) ≫ infinityMap A B=
    overlapMap A B ≫ WeierstrassGluing318.intoInfinity A B := by
  unfold WeierstrassGluing318.intoInfinity infinityMap overlapMap
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (overlapCoefficient_base A B x).symm

lemma glue_compatible (A B:R) : WeierstrassGluing318.intoAffine (a A) (a B) ≫
    finiteMap A B ≫ WeierstrassGluing318.finiteChart A B=
  WeierstrassGluing318.intoInfinity (a A) (a B) ≫ infinityMap A B ≫ WeierstrassGluing318.infinityChart A B := by
  rw [←Category.assoc,←Category.assoc,overlap_finite_map,overlap_infinity_map,Category.assoc,Category.assoc]
  exact congrArg (fun f => overlapMap A B ≫ f) pushout.condition

/-- The actual global coefficient-change morphism, glued from the literal coordinate maps. -/
@[expose] def coefficientMap (A B:R) : WeierstrassGluing318.scheme (a A) (a B) ⟶ WeierstrassGluing318.scheme A B :=
  pushout.desc (finiteMap A B ≫ WeierstrassGluing318.finiteChart A B)
    (infinityMap A B ≫ WeierstrassGluing318.infinityChart A B) (glue_compatible A B)
@[simp] theorem finite_coefficientMap (A B:R) : WeierstrassGluing318.finiteChart (a A) (a B) ≫ coefficientMap A B=
    finiteMap A B ≫ WeierstrassGluing318.finiteChart A B := pushout.inl_desc ..
@[simp] theorem infinity_coefficientMap (A B:R) : WeierstrassGluing318.infinityChart (a A) (a B) ≫ coefficientMap A B=
    infinityMap A B ≫ WeierstrassGluing318.infinityChart A B := pushout.inr_desc ..

lemma finiteMap_base (A B:R) : finiteMap (S:=S) A B ≫ ShortAffineScheme318.structureMap A B=
    ShortAffineScheme318.structureMap (a A) (a B) ≫ Spec.map (CommRingCat.ofHom a) := by
  unfold finiteMap ShortAffineScheme318.structureMap
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (AffineBaseChange318.coefficientMap (S:=S) A B).commutes r
lemma infinityMap_base (A B:R) : infinityMap (S:=S) A B ≫ InfinitySmooth318.structureMap A B=
    InfinitySmooth318.structureMap (a A) (a B) ≫ Spec.map (CommRingCat.ofHom a) := by
  unfold infinityMap InfinitySmooth318.structureMap
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (InfinityBaseChange318.coefficientMap (S:=S) A B).commutes r

/-- The actual coefficient-change square commutes over its original ring map. -/
theorem coefficientMap_base (A B:R) : coefficientMap (S:=S) A B ≫ WeierstrassGluing318.structureMap A B=
    WeierstrassGluing318.structureMap (a A) (a B) ≫ Spec.map (CommRingCat.ofHom a) := by
  apply pushout.hom_ext
  · change WeierstrassGluing318.finiteChart (a A) (a B) ≫ (coefficientMap A B ≫ _)=
      WeierstrassGluing318.finiteChart (a A) (a B) ≫ (_ ≫ _)
    rw [←Category.assoc,finite_coefficientMap,Category.assoc,WeierstrassGluing318.finiteChart_structure,
      finiteMap_base,←Category.assoc,WeierstrassGluing318.finiteChart_structure]
  · change WeierstrassGluing318.infinityChart (a A) (a B) ≫ (coefficientMap A B ≫ _)=
      WeierstrassGluing318.infinityChart (a A) (a B) ≫ (_ ≫ _)
    rw [←Category.assoc,infinity_coefficientMap,Category.assoc,WeierstrassGluing318.infinityChart_structure,
      infinityMap_base,←Category.assoc,WeierstrassGluing318.infinityChart_structure]

lemma coefficient_origin (A B:R) :
    ((InfinityChart318.origin (a A) (a B)).restrictScalars R).comp
      (InfinityBaseChange318.coefficientMap (S:=S) A B)=
    (Algebra.ofId R S).comp (InfinityChart318.origin A B) := by
  apply InfinityChart318.hom_ext
  · simp
  · simp

/-- Actual coefficient change preserves the distinguished infinity section. -/
theorem coefficientMap_infinity (A B:R) :
    WeierstrassGluing318.infinity (a A) (a B) ≫ coefficientMap (S:=S) A B=
      Spec.map (CommRingCat.ofHom a) ≫ WeierstrassGluing318.infinity A B := by
  change InfinitySmooth318.infinity (a A) (a B) ≫
      (WeierstrassGluing318.infinityChart (a A) (a B) ≫ coefficientMap A B)=
    Spec.map (CommRingCat.ofHom a) ≫ InfinitySmooth318.infinity A B ≫ WeierstrassGluing318.infinityChart A B
  rw [infinity_coefficientMap,←Category.assoc,←Category.assoc]
  congr 1
  unfold InfinitySmooth318.infinity infinityMap
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (coefficient_origin (S:=S) A B))

end WeierstrassCoefficientMap318
