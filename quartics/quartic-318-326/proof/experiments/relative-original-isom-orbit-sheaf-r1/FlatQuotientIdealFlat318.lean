module
public import AffineWholeIdealCoefficient318
public section
noncomputable section
namespace FlatQuotientIdealFlat318
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) [hA : Module.Flat R A] [hQ : Module.Flat R (A ⧸ I)]
include hA hQ in
/-- The full original ideal is flat over the coefficient ring. This is
derived from ambient and quotient flatness, without ideal freeness. -/
lemma flat : Module.Flat R I := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro N P _ _ _ _ f hf
  let a := FlatQuotientIdealTensor318.inclusion R A I
  have haN := LinearMap.lTensor_injective_of_exact_of_flat
    (FlatQuotientIdealTensor318.quotient R A I) (Ideal.Quotient.mkₐ_surjective R I)
    a Subtype.val_injective (FlatQuotientIdealTensor318.exact R A I) N
  have hs : (a.lTensor P).comp (f.rTensor I)=(f.rTensor A).comp (a.lTensor N) := by
    ext n i
    rfl
  intro x y h
  apply haN
  apply Module.Flat.rTensor_preserves_injective_linearMap f hf
  change ((f.rTensor A).comp (a.lTensor N)) x=((f.rTensor A).comp (a.lTensor N)) y
  rw [← hs]
  exact congrArg (a.lTensor P) h
end FlatQuotientIdealFlat318
