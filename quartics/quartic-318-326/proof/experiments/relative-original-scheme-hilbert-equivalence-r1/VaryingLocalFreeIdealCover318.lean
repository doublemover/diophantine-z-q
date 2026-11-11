module
public import AffineCoefficientCover318
public import VaryingAllPointLocalFreeIdeals318
public import VaryingSourceMapComposition318
public section
noncomputable section
namespace VaryingLocalFreeIdealCover318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- A geometric local-free hypothesis on a LITERAL full quotient ideal:
a complete actual affine coefficient cover where its extensions are free.
No parameter point or classifying map is part of this input. -/
structure Data (I : Ideal (S ⊗[R] A)) where
  coefficients : AffineCoefficientCover318.Data R S
  free : ∀ i, Nonempty (Module.Basis ι (coefficients.ring i)
    ((coefficients.ring i ⊗[R] A) ⧸ Ideal.map
      (VaryingNormalizedIdealBaseChange318.sourceMap R A S (coefficients.ring i)
        (coefficients.coefficient i)).toRingHom I))
variable (I : Ideal (S ⊗[R] A)) (C : Data R A ι S I)
@[expose] def localIdeal (i : C.coefficients.Index) :
    VaryingFreeIdealClassifyingMap318.IdealData R A ι (C.coefficients.ring i) :=
  ⟨Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S (C.coefficients.ring i)
    (C.coefficients.coefficient i)).toRingHom I,C.free i⟩
@[expose] def localMap (i : C.coefficients.Index) : Spec (C.coefficients.ring i) ⟶
    VaryingWordChartGluing318.scheme R A ι :=
  VaryingFreeIdealClassifyingMap318.classify R A ι (C.coefficients.ring i) (localIdeal R A ι S I C i)
/-- Every actual point supplies this geometric hypothesis by its proved
whole affine cover; this is not the definition of the hypothesis. -/
@[expose] def ofPoint (x : VaryingParameterPoint318.Point R A ι S) :
    Data R A ι S (VaryingParameterPointIdeal318.ideal R A ι S x) where
  coefficients :=
    { Index := VaryingPointAffineChartCover318.index R A ι S x
      ring := VaryingPointAffineChartCover318.ring R A ι S x
      algebra := fun i => inferInstance
      coefficient := VaryingPointAffineChartCover318.coefficient R A ι S x
      open_map := fun i => by
        rw [show Spec.map (CommRingCat.ofHom (VaryingPointAffineChartCover318.coefficient R A ι S x i).toRingHom)=
          (VaryingPointAffineChartCover318.cover R A ι S x).f i from VaryingPointAffineChartCover318.coefficient_spec R A ι S x i]
        infer_instance
      covers := by
        intro t
        obtain ⟨i,y,hy⟩ := (VaryingPointAffineChartCover318.cover R A ι S x).openCover.exists_eq t
        refine ⟨i,y,?_⟩
        rw [VaryingPointAffineChartCover318.coefficient_spec]
        exact hy }
  free := VaryingAllPointLocalFreeIdeals318.free_extended_ideal R A ι S x
end VaryingLocalFreeIdealCover318
