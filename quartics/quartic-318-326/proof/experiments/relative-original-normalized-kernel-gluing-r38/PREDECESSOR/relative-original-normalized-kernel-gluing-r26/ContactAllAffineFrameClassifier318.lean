module
public import ContactFrameAffineCoefficient318
public section
noncomputable section
namespace ContactAllAffineFrameClassifier318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318 OriginalLineFrameUnitTorsor318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
abbrev parameter := (ContactArbitraryNowhereZeroOpen318.locus R c L).toScheme
abbrev projection : parameter R c L ⟶ Spec R :=
  (ContactArbitraryNowhereZeroOpen318.locus R c L).ι ≫
    AffineAlgebraSchemeEquiv318.base R (ContactArbitrarySectionParameter318.parameterRing R c L)
/-- Every affine SCHEME test, without a separately supplied rational algebra
structure, is classified by the SAME original open parameter and p-first line. -/
@[expose] def equivalence (S : CommRingCat.{0}) (b : Spec S ⟶ Spec R) :
    AffineRelativeFrameClassifier318.Point (projection R c L) S b ≃
      Frames (LineSheafPullback318.line
        (pullback.fst (ContactCanonicalCoefficientFrame318.projection R c) b) L) := by
  letI := ContactFrameAffineCoefficient318.algebra R S b
  have e := ContactCanonicalTrivializationParameter318.equivalence R c L S
    (ContactFrameAffineCoefficient318.hom R S b)
  change {x : Spec S ⟶ parameter R c L //
      x ≫ projection R c L=Spec.map (Spec.preimage b)} ≃
    Frames (LineSheafPullback318.line
      (pullback.fst (ContactCanonicalCoefficientFrame318.projection R c)
        (Spec.map (Spec.preimage b))) L) at e
  simpa only [Spec.map_preimage] using e
lemma natural (S T : CommRingCat.{0}) (g : Spec T ⟶ Spec S)
    (b : Spec S ⟶ Spec R) (a : Spec T ⟶ Spec R) (hg : g ≫ b=a)
    (x : AffineRelativeFrameClassifier318.Point (projection R c L) S b) :
    OriginalFramePathTransport318.transport L
      (RelativeSchemeCoefficient318.map (ContactCanonicalCoefficientFrame318.projection R c) b a g hg)
      (pullback.fst (ContactCanonicalCoefficientFrame318.projection R c) b)
      (pullback.fst (ContactCanonicalCoefficientFrame318.projection R c) a)
      (RelativeSchemeCoefficient318.map_fst _ _ _ _ _) (equivalence R c L S b x)=
    equivalence R c L T a (AffineRelativeFrameClassifier318.pointMap (projection R c L) S T g b a hg x) := by
  obtain ⟨f,rfl⟩ := Spec.map_surjective b
  obtain ⟨k,rfl⟩ := Spec.map_surjective g
  subst a
  rw [←Spec.map_comp]
  letI : Algebra ℚ S := (f.hom.comp (algebraMap ℚ R)).toAlgebra
  letI : Algebra ℚ T := ((f ≫ k).hom.comp (algebraMap ℚ R)).toAlgebra
  let fQ : R →ₐ[ℚ] S := { __ := f.hom, commutes' := fun _ => rfl }
  let kQ : S →ₐ[ℚ] T := { __ := k.hom, commutes' := fun _ => rfl }
  have xQ : ContactTrivializationAffinePoints318.Points R c L S fQ := x
  have hn := ContactCanonicalTrivializationParameter318.natural R c L S fQ T kQ xQ
  simpa only [equivalence,ContactFrameAffineCoefficient318.algebra,
    ContactFrameAffineCoefficient318.hom,ContactFrameAffineCoefficient318.preimage_map,
    ContactCanonicalCoefficientFrame318.base,ContactCanonicalTrivializationParameter318.pointMap,
    AffineOpenPointNaturality318.map,ContactHZeroCoefficientFunctor318.coefficientArrow,
    ContactCanonicalCoefficientNaturality318.coefficient,AffineRelativeFrameClassifier318.pointMap,
    fQ,kQ,xQ] using hn
/-- The affine datum consumed by whole-scheme gluing is CONSTRUCTED from
the earlier original parameter. It is not an assumed representability witness. -/
@[expose] def data : AffineRelativeFrameClassifier318.Data
    (ContactCanonicalCoefficientFrame318.projection R c) L (projection R c L) where
  equivalence := equivalence R c L
  natural := natural R c L
end ContactAllAffineFrameClassifier318
