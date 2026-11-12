module
public import ChartNegation318
import all WeierstrassGluing318
public section
noncomputable section
namespace GluedNegation318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassGluing318 ChartNegation318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R]

@[expose] def finiteNeg (A B:R) : ShortAffineScheme318.scheme A B ⟶ ShortAffineScheme318.scheme A B :=
  Spec.map (CommRingCat.ofHom (affineNeg A B).toRingHom)
@[expose] def infinityNeg (A B:R) : InfinitySmooth318.scheme A B ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom (ChartNegation318.infinityNeg A B).toRingHom)
@[expose] def overlapNeg (A B:R) : overlap A B ⟶ overlap A B :=
  Spec.map (CommRingCat.ofHom (ChartNegation318.overlapNeg A B).toRingHom)

theorem finite_twice (A B:R) : finiteNeg A B ≫ finiteNeg A B=𝟙 _ := by
  dsimp only [finiteNeg,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (affineNeg_twice A B))
theorem infinity_twice (A B:R) : infinityNeg A B ≫ infinityNeg A B=𝟙 _ := by
  dsimp only [infinityNeg,InfinitySmooth318.scheme]
  rw [←Spec.map_comp,←Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (infinityNeg_twice A B))

theorem overlap_finite (A B:R) : overlapNeg A B ≫ intoAffine A B=
    intoAffine A B ≫ finiteNeg A B := by
  rw [intoAffine_eq]
  dsimp only [overlapNeg,finiteNeg,ShortAffineScheme318.scheme]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (affine_overlap A B))
theorem overlap_infinity (A B:R) : overlapNeg A B ≫ intoInfinity A B=
    intoInfinity A B ≫ infinityNeg A B := by
  dsimp only [overlapNeg,infinityNeg,intoInfinity,InfinitySmooth318.scheme]
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (infinity_overlap A B))

/-- Actual global involution on the genuine glued Weierstrass Scheme. -/
@[expose] def negation (A B:R) : scheme A B ⟶ scheme A B :=
  pushout.desc (finiteNeg A B ≫ finiteChart A B) (infinityNeg A B ≫ infinityChart A B) (by
    rw [←Category.assoc,←overlap_finite,Category.assoc,
      show intoAffine A B ≫ finiteChart A B=intoInfinity A B ≫ infinityChart A B from
        pushout.condition,←Category.assoc,overlap_infinity,Category.assoc])

@[simp] theorem finiteChart_negation (A B:R) : finiteChart A B ≫ negation A B=
    finiteNeg A B ≫ finiteChart A B := pushout.inl_desc ..
@[simp] theorem infinityChart_negation (A B:R) : infinityChart A B ≫ negation A B=
    infinityNeg A B ≫ infinityChart A B := pushout.inr_desc ..

theorem negation_twice (A B:R) : negation A B ≫ negation A B=𝟙 _ := by
  apply pushout.hom_ext
  · change finiteChart A B ≫ (negation A B ≫ negation A B)=finiteChart A B ≫ 𝟙 _
    rw [←Category.assoc,finiteChart_negation,Category.assoc,finiteChart_negation,
      ←Category.assoc,finite_twice,Category.id_comp,Category.comp_id]
  · change infinityChart A B ≫ (negation A B ≫ negation A B)=infinityChart A B ≫ 𝟙 _
    rw [←Category.assoc,infinityChart_negation,Category.assoc,infinityChart_negation,
      ←Category.assoc,infinity_twice,Category.id_comp,Category.comp_id]

/-- The involution is an actual Scheme automorphism, in every characteristic. -/
@[expose] def negationIso (A B:R) : scheme A B ≅ scheme A B where
  hom:=negation A B
  inv:=negation A B
  hom_inv_id:=negation_twice A B
  inv_hom_id:=negation_twice A B

theorem finite_over_base (A B:R) : finiteNeg A B ≫ ShortAffineScheme318.structureMap A B=
    ShortAffineScheme318.structureMap A B := by
  dsimp only [finiteNeg,ShortAffineScheme318.scheme,ShortAffineScheme318.structureMap]
  rw [←Spec.map_comp]
  congr 1
  ext r
  exact (affineNeg A B).commutes r

theorem infinity_over_base (A B:R) : infinityNeg A B ≫ InfinitySmooth318.structureMap A B=
    InfinitySmooth318.structureMap A B := by
  dsimp only [infinityNeg,InfinitySmooth318.scheme,InfinitySmooth318.structureMap]
  rw [←Spec.map_comp]
  congr 1
  ext r
  exact (ChartNegation318.infinityNeg A B).commutes r

theorem negation_over_base (A B:R) : negation A B ≫ structureMap A B=structureMap A B := by
  apply pushout.hom_ext
  · change finiteChart A B ≫ (negation A B ≫ structureMap A B)=finiteChart A B ≫ structureMap A B
    rw [←Category.assoc,finiteChart_negation,Category.assoc,finiteChart_structure,finite_over_base]
  · change infinityChart A B ≫ (negation A B ≫ structureMap A B)=infinityChart A B ≫ structureMap A B
    rw [←Category.assoc,infinityChart_negation,Category.assoc,infinityChart_structure,infinity_over_base]

/-- The genuine zero section in the infinity chart is fixed. -/
theorem infinity_origin_fixed (A B:R) :
    InfinitySmooth318.infinity A B ≫ infinityNeg A B=InfinitySmooth318.infinity A B := by
  have hh : (InfinityChart318.origin A B).comp (ChartNegation318.infinityNeg A B)=
      InfinityChart318.origin A B := by
    apply InfinityChart318.hom_ext <;> simp
  dsimp only [InfinitySmooth318.infinity,infinityNeg,InfinitySmooth318.scheme]
  rw [←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom hh)

/-- The actual global infinity section is fixed by the actual involution. -/
theorem infinity_fixed (A B:R) : infinity A B ≫ negation A B=infinity A B := by
  dsimp only [infinity]
  rw [Category.assoc,infinityChart_negation,←Category.assoc,infinity_origin_fixed]

/-- Literal source-family global automorphism, not merely a field-valued operation. -/
@[expose] def literalNegationIso (N:ℕ) : literalScheme N ≅ literalScheme N :=
  negationIso (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N)

end GluedNegation318
