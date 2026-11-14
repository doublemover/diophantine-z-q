module
public import IntegralRationalInfinityMap318
public import IntegralRationalFiniteAtlas318
public import IntegralGluedModel318
public import CompletedCharacterGlobal318
public section
noncomputable section
namespace IntegralRationalGlobalComparison318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open IntegralGluedModel318 IntegralRationalFullOverlap318 IntegralInfinityOriginalField318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Transport a commuting ring square contravariantly before specializing
any of the concrete nested overlap carriers. -/
private theorem spec_inverse_square {A B C D : CommRingCat}
    (f : A ⟶ B) (g : C ⟶ D) (eA : A ≅ C) (eB : B ≅ D)
    (h : f ≫ eB.hom = eA.hom ≫ g) :
    (Scheme.Spec.mapIso eB.symm.op).inv ≫ Spec.map f =
      Spec.map g ≫ (Scheme.Spec.mapIso eA.symm.op).inv := by
  change Spec.map eB.hom ≫ Spec.map f = Spec.map g ≫ Spec.map eA.hom
  rw [←Spec.map_comp, ←Spec.map_comp, h]

variable (c : Fin 4 → ℚˣ)

/-- These are the same source restrictions used to construct overlapEquiv,
not newly chosen scalar actions on either overlap. -/
local instance sourceOverlapAlgebra :
    Algebra (IntegralSourceBranches318.SourceOrder ℚ c)
      (IntegralOverlapChartMaps318.Overlap ℚ c) :=
  IntegralFullOverlapLocalization318.sourceAlgebra ℚ c
local instance originalSourceAlgebra :
    Algebra (IntegralSourceBranches318.SourceOrder ℚ c)
      (ContactKummerOrder318.OpenOrder c) :=
  IntegralRationalFullOverlap318.originalAlgebra c

/-- These chart identifications are the contravariant spectra of the original
ring equivalences, not abstract affine isomorphisms chosen from dimensions. -/
@[expose] def finiteIso : finiteScheme ℚ c ≅
    Spec (CommRingCat.of (ContactKummerOrder318.SourceOrder c)) :=
  Scheme.Spec.mapIso (sourceEquiv c).toRingEquiv.toCommRingCatIso.symm.op
@[expose] def infinityIso : infinityScheme ℚ c ≅
    ReciprocalInfinityNormalization318.neighborhood c :=
  Scheme.Spec.mapIso (rationalOrderEquiv c).toRingEquiv.toCommRingCatIso.symm.op
@[expose] def overlapIso : commonScheme ℚ c ≅ ContactKummerCover318.cover c :=
  Scheme.Spec.mapIso (overlapEquiv c).toRingEquiv.toCommRingCatIso.symm.op

theorem finite_inverse_square :
    (overlapIso c).inv ≫ intoFinite ℚ c =
      ContactOverlapMaps318.sourceInclusion c ≫ (finiteIso c).inv :=
  IntegralRationalFiniteAtlas318.finite_square c

/-- This equality uses all three signed infinity generators, not only the
reciprocal coordinate or an equality after squaring the roots. -/
theorem infinity_inverse_square :
    (overlapIso c).inv ≫ intoInfinity ℚ c =
      ContactOverlapMaps318.infinityInclusion c ≫ (infinityIso c).inv := by
  apply spec_inverse_square
    (CommRingCat.ofHom (IntegralOverlapChartMaps318.infinityMap ℚ c).toRingHom)
    (CommRingCat.ofHom (InfinityOverlapLocalization318.toOpen c))
    (rationalOrderEquiv c).toRingEquiv.toCommRingCatIso
    (overlapEquiv c).toRingEquiv.toCommRingCatIso
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact IntegralRationalInfinityMap318.infinity_restriction c a

theorem finite_square :
    intoFinite ℚ c ≫ (finiteIso c).hom =
      (overlapIso c).hom ≫ ContactOverlapMaps318.sourceInclusion c := by
  apply (cancel_epi (overlapIso c).inv).mp
  rw [←Category.assoc,finite_inverse_square]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

theorem infinity_square :
    intoInfinity ℚ c ≫ (infinityIso c).hom =
      (overlapIso c).hom ≫ ContactOverlapMaps318.infinityInclusion c := by
  apply (cancel_epi (overlapIso c).inv).mp
  rw [←Category.assoc,infinity_inverse_square]
  simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]

theorem forward_compatible :
    intoFinite ℚ c ≫ ((finiteIso c).hom ≫ SourceGlobalAffine318.chartEmbedding c) =
    intoInfinity ℚ c ≫ ((infinityIso c).hom ≫ InfinityGlobalScheme318.chartEmbedding c) := by
  rw [←Category.assoc,finite_square,Category.assoc,ContactOverlapMaps318.maps_agree,
    ←Category.assoc,←infinity_square,Category.assoc]

/-- The entire original integral pushout over Q maps to the original global
normalization through its specified finite and infinity embeddings. -/
@[expose] def toOriginal : scheme ℚ c ⟶ ContactGlobalSmooth318.Model c :=
  pushout.desc ((finiteIso c).hom ≫ SourceGlobalAffine318.chartEmbedding c)
    ((infinityIso c).hom ≫ InfinityGlobalScheme318.chartEmbedding c) (forward_compatible c)

@[simp] theorem finite_toOriginal :
    finiteChart ℚ c ≫ toOriginal c =
      (finiteIso c).hom ≫ SourceGlobalAffine318.chartEmbedding c := pushout.inl_desc ..
@[simp] theorem infinity_toOriginal :
    infinityChart ℚ c ≫ toOriginal c =
      (infinityIso c).hom ≫ InfinityGlobalScheme318.chartEmbedding c := pushout.inr_desc ..

theorem backward_compatible :
    ContactOverlapMaps318.sourceInclusion c ≫ ((finiteIso c).inv ≫ finiteChart ℚ c) =
    ContactOverlapMaps318.infinityInclusion c ≫ ((infinityIso c).inv ≫ infinityChart ℚ c) := by
  rw [←Category.assoc,←finite_inverse_square,Category.assoc]
  rw [show intoFinite ℚ c ≫ finiteChart ℚ c = intoInfinity ℚ c ≫ infinityChart ℚ c
    from pushout.condition]
  rw [←Category.assoc,infinity_inverse_square,Category.assoc]

@[expose] def localBack : (b : Bool) → (ContactGlobalSmooth318.cover c).X b ⟶ scheme ℚ c
  | false => (finiteIso c).inv ≫ finiteChart ℚ c
  | true => (infinityIso c).inv ≫ infinityChart ℚ c

theorem localBack_compatible (b d : Bool) :
    pullback.fst ((ContactGlobalSmooth318.cover c).f b)
      ((ContactGlobalSmooth318.cover c).f d) ≫ localBack c b =
    pullback.snd _ _ ≫ localBack c d := by
  cases b <;> cases d
  · exact CompletedCharacterGlobal318.diagonal_compatibility _ _
  · exact CompletedCharacterGlobal318.compatibility_of_actual_pullback
      (ContactFullOverlap318.actual_pullback c) _ _ (backward_compatible c)
  · exact CompletedCharacterGlobal318.compatibility_of_actual_pullback
      (ContactFullOverlap318.actual_pullback c).flip _ _ (backward_compatible c).symm
  · exact CompletedCharacterGlobal318.diagonal_compatibility _ _

/-- The inverse uses the whole original two-chart cover and its actual full
intersection. It is not a map defined only on a dense open. -/
@[expose] def fromOriginal : ContactGlobalSmooth318.Model c ⟶ scheme ℚ c :=
  (ContactGlobalSmooth318.cover c).glueMorphisms (localBack c) (localBack_compatible c)

@[simp] theorem finite_fromOriginal :
    SourceGlobalAffine318.chartEmbedding c ≫ fromOriginal c =
      (finiteIso c).inv ≫ finiteChart ℚ c :=
  (ContactGlobalSmooth318.cover c).ι_glueMorphisms (localBack c) (localBack_compatible c) false
@[simp] theorem infinity_fromOriginal :
    InfinityGlobalScheme318.chartEmbedding c ≫ fromOriginal c =
      (infinityIso c).inv ≫ infinityChart ℚ c :=
  (ContactGlobalSmooth318.cover c).ι_glueMorphisms (localBack c) (localBack_compatible c) true

theorem to_from : toOriginal c ≫ fromOriginal c = 𝟙 _ := by
  apply pushout.hom_ext
  · change finiteChart ℚ c ≫ (toOriginal c ≫ fromOriginal c) = finiteChart ℚ c ≫ 𝟙 _
    rw [←Category.assoc,finite_toOriginal,Category.assoc,finite_fromOriginal]
    simp only [Iso.hom_inv_id_assoc,Category.comp_id]
  · change infinityChart ℚ c ≫ (toOriginal c ≫ fromOriginal c) = infinityChart ℚ c ≫ 𝟙 _
    rw [←Category.assoc,infinity_toOriginal,Category.assoc,infinity_fromOriginal]
    simp only [Iso.hom_inv_id_assoc,Category.comp_id]

theorem from_to : fromOriginal c ≫ toOriginal c = 𝟙 _ := by
  apply (ContactGlobalSmooth318.cover c).hom_ext
  intro b
  cases b
  · change SourceGlobalAffine318.chartEmbedding c ≫ (fromOriginal c ≫ toOriginal c) =
      SourceGlobalAffine318.chartEmbedding c ≫ 𝟙 _
    rw [←Category.assoc,finite_fromOriginal,Category.assoc,finite_toOriginal]
    simp only [Iso.inv_hom_id_assoc,Category.comp_id]
  · change InfinityGlobalScheme318.chartEmbedding c ≫ (fromOriginal c ≫ toOriginal c) =
      InfinityGlobalScheme318.chartEmbedding c ≫ 𝟙 _
    rw [←Category.assoc,infinity_fromOriginal,Category.assoc,infinity_toOriginal]
    simp only [Iso.inv_hom_id_assoc,Category.comp_id]

/-- The actual integral glued model specialized to Q IS the original global
contact normalization, with its original signed finite and infinity charts. -/
@[expose] def originalModelIso : scheme ℚ c ≅ ContactGlobalSmooth318.Model c where
  hom := toOriginal c
  inv := fromOriginal c
  hom_inv_id := to_from c
  inv_hom_id := from_to c

/-- Any specified rational ring equivalence respects the unique Q scalar
map. This lemma is used with the exact chart equivalences above. -/
theorem rational_chart_structure {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (e : A ≃+* B) :
    Spec.map e.toCommRingCatIso.inv ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ B)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) := by
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact e.symm.toRingHom.map_rat_algebraMap r

/-- The global comparison retains the original Q-structure morphism, in
addition to the whole underlying scheme and both signed chart maps. -/
theorem over_Q :
    toOriginal c ≫ ((ContactProjectiveModel318.coverMap c).fromNormalization ≫
      ProjectiveJLine318.structureMap ℚ) = structureMap ℚ c := by
  apply pushout.hom_ext
  · change finiteChart ℚ c ≫ (toOriginal c ≫ _) = finiteChart ℚ c ≫ structureMap ℚ c
    rw [←Category.assoc,finite_toOriginal,Category.assoc,
      SourceGlobalAffine318.chartEmbedding_over_Q,finiteChart_structure]
    exact rational_chart_structure (sourceEquiv c).toRingEquiv
  · change infinityChart ℚ c ≫ (toOriginal c ≫ _) = infinityChart ℚ c ≫ structureMap ℚ c
    rw [←Category.assoc,infinity_toOriginal,Category.assoc,
      InfinityStructureSmooth318.chartEmbedding_over_Q,infinityChart_structure]
    exact rational_chart_structure (rationalOrderEquiv c).toRingEquiv
end IntegralRationalGlobalComparison318
