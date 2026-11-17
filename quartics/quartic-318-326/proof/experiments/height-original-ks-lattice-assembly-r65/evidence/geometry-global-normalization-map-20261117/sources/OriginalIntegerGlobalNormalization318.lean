module
public import OriginalIntegerNormalizationOverlapCompatibility318
public import OriginalIntegerClosureGluing318
public import OriginalIntegerGluedModel318
public section
noncomputable section
namespace OriginalIntegerGlobalNormalization318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ)
abbrev source := OriginalIntegerClosureGluing318.model c
abbrev target := OriginalIntegerGluedModel318.model c
abbrev d := OriginalIntegerReciprocalCharts318.integralTwist c
abbrev a := OriginalIntegerAffineModel318.contacts

@[expose] def finiteMap :
    Spec (CommRingCat.of (OriginalIntegerFiniteClosure318.Closure c)) ⟶
      Spec (CommRingCat.of (OriginalIntegerAffineModel318.Order c)) :=
  Spec.map (CommRingCat.ofHom (OriginalIntegerNormalizationMap318.toClosure c).toRingHom)

@[expose] def infinityMap :
    Spec (CommRingCat.of (OriginalIntegerReciprocalNormalization318.Closure c)) ⟶
      Spec (CommRingCat.of (OriginalIntegerReciprocalCharts318.ReciprocalOrder c)) :=
  Spec.map (CommRingCat.ofHom
    (OriginalIntegerReciprocalOrderNormalization318.toClosure c).toRingHom)

@[expose] def overlapMap :
    Spec (CommRingCat.of (OriginalIntegerNormalizedOverlap318.Overlap c)) ⟶
      IntegralFourRootGluing318.overlap ℤ (d c) a :=
  Spec.map (CommRingCat.ofHom
    (OriginalIntegerNormalizationOverlapCompatibility318.toOverlap c).toRingHom)

private theorem spec_square {A B C D : Type} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] (f : A →+* B) (r : A →+* C)
    (l : B →+* D) (m : C →+* D) (h : l.comp f = m.comp r) :
    Spec.map (CommRingCat.ofHom l) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom m) ≫ Spec.map (CommRingCat.ofHom r) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun q : A →+* D => Spec.map (CommRingCat.ofHom q)) h

/-- Exact finite normalization square, obtained from the actual ring maps. -/
theorem finite_square :
    OriginalIntegerNormalizedOverlap318.intoFinite c ≫ finiteMap c =
      overlapMap c ≫ IntegralFourRootGluing318.intoFinite ℤ (d c) a := by
  apply spec_square
  apply RingHom.ext
  intro z
  exact (OriginalIntegerNormalizationOverlapCompatibility318.finite_square c z).symm

/-- Exact reciprocal normalization square over the same Laurent overlap. -/
theorem infinity_square :
    OriginalIntegerReciprocalNormalization318.intoInfinity c ≫ infinityMap c =
      overlapMap c ≫ IntegralFourRootGluing318.intoInfinity ℤ (d c) a := by
  apply spec_square
  apply RingHom.ext
  intro z
  exact (OriginalIntegerNormalizationOverlapCompatibility318.infinity_square c z).symm

@[expose] def finiteProjection :
    Spec (CommRingCat.of (OriginalIntegerFiniteClosure318.Closure c)) ⟶ target c :=
  finiteMap c ≫ IntegralFourRootGluing318.finiteChart ℤ (d c) a

@[expose] def infinityProjection :
    Spec (CommRingCat.of (OriginalIntegerReciprocalNormalization318.Closure c)) ⟶ target c :=
  infinityMap c ≫ IntegralFourRootGluing318.infinityChart ℤ (d c) a

theorem gluing_condition :
    OriginalIntegerNormalizedOverlap318.intoFinite c ≫ finiteProjection c =
      OriginalIntegerReciprocalNormalization318.intoInfinity c ≫ infinityProjection c := by
  unfold finiteProjection infinityProjection
  rw [← Category.assoc, finite_square, Category.assoc,
    pushout.condition, ← Category.assoc, ← infinity_square, Category.assoc]

/-- A genuine map from the already glued literal integral closures to the
original whole-order model. Finiteness still requires full chart preimages. -/
@[expose] def normalization : source c ⟶ target c :=
  pushout.desc (finiteProjection c) (infinityProjection c) (gluing_condition c)

theorem finite_restriction :
    OriginalIntegerClosureGluing318.finiteChart c ≫ normalization c = finiteProjection c := by
  exact pushout.inl_desc _ _ _

theorem infinity_restriction :
    OriginalIntegerClosureGluing318.infinityChart c ≫ normalization c = infinityProjection c := by
  exact pushout.inr_desc _ _ _

end OriginalIntegerGlobalNormalization318
