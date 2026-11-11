module
public import VaryingGlobalFreeQuotientEquiv318
public section
noncomputable section
namespace VaryingFreePointIdealSeparation318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
/-- If one of two actual points is free and their WHOLE intrinsic ideals
agree, both points are free and hence equal by the genuine inverse. -/
lemma eq_of_ideal {x y : VaryingParameterPoint318.Point R A ι S}
    (hx : Nonempty (Module.Basis ι S ((S ⊗[R] A) ⧸ VaryingParameterPointIdeal318.ideal R A ι S x)))
    (h : VaryingParameterPointIdeal318.ideal R A ι S x=VaryingParameterPointIdeal318.ideal R A ι S y) : x=y := by
  have hy : Nonempty (Module.Basis ι S ((S ⊗[R] A) ⧸ VaryingParameterPointIdeal318.ideal R A ι S y)) := by
    rw [← h]
    exact hx
  let x' : VaryingFreeParameterPoints318.FreePoint R A ι S := ⟨x,hx⟩
  let y' : VaryingFreeParameterPoints318.FreePoint R A ι S := ⟨y,hy⟩
  have hi : VaryingFreeParameterPoints318.recover R A ι S x'=
      VaryingFreeParameterPoints318.recover R A ι S y' := Subtype.ext h
  have hxy : x'=y' := by
    rw [← VaryingFreePointGlobalInverse318.classify_recover R A ι S x',
      ← VaryingFreePointGlobalInverse318.classify_recover R A ι S y',hi]
  exact congrArg Subtype.val hxy
end VaryingFreePointIdealSeparation318
