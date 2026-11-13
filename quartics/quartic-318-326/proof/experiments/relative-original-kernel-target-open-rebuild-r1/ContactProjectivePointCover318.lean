module
public import ContactProjectiveInputRecovery318
public section
noncomputable section
namespace ContactProjectivePointCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  (x : ContactProjectiveParameterPoint318.Point c n S)
abbrev pulled := (ContactProjectiveQuotientParameter318.cover c n).pullback₁ x.val
@[expose] def cover : (Spec S).AffineOpenCover := (pulled c n S x).affineRefinement
abbrev index := (cover c n S x).I₀
variable (i : index c n S x)
abbrev ring : CommRingCat.{0} := (cover c n S x).X i
@[expose] instance algebra : Algebra ℚ (ring c n S x i) :=
  ((Spec.preimage ((cover c n S x).f i)).hom.comp (algebraMap ℚ S)).toAlgebra
@[expose] def coefficient : S →ₐ[ℚ] ring c n S x i where
  __ := (Spec.preimage ((cover c n S x).f i)).hom
  commutes' _ := rfl
lemma coefficient_spec : Spec.map (CommRingCat.ofHom (coefficient c n S x i).toRingHom)=(cover c n S x).f i :=
  Spec.map_preimage _
abbrev chart : Chart := i.1
@[expose] def chartMap : Spec (ring c n S x i) ⟶ ContactQuotientUniversalOriginal318.parameter c (chart c n S x i) n :=
  ((pulled c n S x).X i.1).affineOpenCover.f i.2 ≫
    pullback.snd x.val (ContactProjectiveQuotientParameter318.into c n i.1)
lemma chart_square : chartMap c n S x i ≫ ContactProjectiveQuotientParameter318.into c n (chart c n S x i)=
    Spec.map (CommRingCat.ofHom (coefficient c n S x i).toRingHom) ≫ x.val := by
  rw [coefficient_spec]
  change (((pulled c n S x).X i.1).affineOpenCover.f i.2 ≫
    pullback.snd x.val (ContactProjectiveQuotientParameter318.into c n i.1)) ≫ _=
    (((pulled c n S x).X i.1).affineOpenCover.f i.2 ≫
      pullback.fst x.val (ContactProjectiveQuotientParameter318.into c n i.1)) ≫ _
  rw [Category.assoc,Category.assoc,pullback.condition]
lemma chart_over : chartMap c n S x i ≫ ContactQuotientUniversalOriginal318.structureMap c (chart c n S x i) n=
    VaryingSourceCoefficientPullback318.base ℚ (ring c n S x i) := by
  rw [← ContactProjectiveParameterStructure318.into_structureMap,← Category.assoc,chart_square,
    Category.assoc,x.property]
  exact VaryingSourceCoefficientPullback318.coefficient_base ℚ S _ (coefficient c n S x i)
@[expose] def localPoint : VaryingParameterPoint318.Point ℚ (ContactQuotientChart318.ring c (chart c n S x i))
    (Fin n) (ring c n S x i) := ⟨chartMap c n S x i,chart_over c n S x i⟩
/-- The full affine refinement covers EVERY point of the coefficient
spectrum, even when the global parameter point crosses source charts. -/
@[expose] def coefficients : AffineCoefficientCover318.Data ℚ S where
  Index := index c n S x
  ring := ring c n S x
  algebra := algebra c n S x
  coefficient := coefficient c n S x
  open_map i := by rw [coefficient_spec]; infer_instance
  covers y := by
    obtain ⟨i,z,hz⟩ := (cover c n S x).openCover.exists_eq y
    refine ⟨i,?_⟩
    rw [coefficient_spec]
    exact ⟨z,hz⟩
end ContactProjectivePointCover318
