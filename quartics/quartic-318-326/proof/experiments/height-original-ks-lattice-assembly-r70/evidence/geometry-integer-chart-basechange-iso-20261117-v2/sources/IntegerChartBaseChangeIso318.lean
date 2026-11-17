module
public import IntegerRationalTensorNaturality318
public section
noncomputable section
namespace IntegerChartBaseChangeIso318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
variable {A : Type} [CommRing A] {X : Scheme}
  (s : X ⟶ Spec (CommRingCat.of ℤ)) (a : Spec (CommRingCat.of A) ⟶ X)
  (ha : a ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ A)))
abbrev base := Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))

/-- A projection-friendly version of the canonical chart base-change
identification, keeping the structure-map equality as an explicit pullback
congruence rather than hiding it in an equality cast. -/
@[expose] def iso : pullback a (pullback.fst s base) ≅
    Spec (CommRingCat.of (A ⊗[ℤ] ℚ)) :=
  pullbackRightPullbackFstIso s base a ≪≫
    pullback.congrHom ha rfl ≪≫ pullbackSpecIso ℤ A ℚ

@[reassoc] theorem hom_original : (iso s a ha).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[ℤ] ℚ))) =
      pullback.fst a (pullback.fst s base) := by
  simp only [iso, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst',
    pullback.congrHom_hom, pullback.map_fst, Category.comp_id,
    pullbackRightPullbackFstIso_hom_fst]

@[reassoc] theorem hom_rational : (iso s a ha).hom ≫
    Spec.map (CommRingCat.ofHom (IntegerRationalTensorNaturality318.rationalCoefficient A)) =
      pullback.snd a (pullback.fst s base) ≫ pullback.snd s base := by
  simp only [iso, Iso.trans_hom, Category.assoc,
    IntegerRationalTensorNaturality318.rationalCoefficient, pullbackSpecIso_hom_snd,
    pullback.congrHom_hom, pullback.map_snd, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd]

end IntegerChartBaseChangeIso318
