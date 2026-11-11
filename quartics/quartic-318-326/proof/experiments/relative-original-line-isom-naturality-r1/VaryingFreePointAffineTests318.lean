module
public import VaryingFreePointChartInverse318
public import AffineSchemeAlgebraMap318
public section
noncomputable section
namespace VaryingFreePointAffineTests318
open AlgebraicGeometry CategoryTheory
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingFreeParameterPoints318.FreePoint R A ι S)
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
variable (w : ι → List A)
local notation "N" => VaryingNormalizedWordParameter318.ring R A ι w
local notation "c" => VaryingSourceCoefficientPullback318.coefficientChange R S T f
variable (g : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of N))
  (h : c ≫ x.val.val=g ≫ VaryingWordChartGluing318.into R A ι w)
include h
lemma chart_base : g ≫ VaryingSourceCoefficientPullback318.base R N=
    VaryingSourceCoefficientPullback318.base R T := by
  rw [← VaryingWordParameterStructure318.into_structureMap R A ι w,← Category.assoc,← h,
    Category.assoc,x.val.property,VaryingSourceCoefficientPullback318.coefficient_base]
/-- Reclassification is the identity on every affine test that actually
lands in a parameter chart. All coefficient/source maps are retained. -/
lemma test_identity : c ≫ (VaryingFreeParameterPoints318.classify R A ι S
    (VaryingFreeParameterPoints318.recover R A ι S x)).val.val=c ≫ x.val.val := by
  let γ := AffineSchemeAlgebraMap318.hom R N T g (chart_base R A ι S x T f w g h)
  have hγ : Spec.map (CommRingCat.ofHom γ.toRingHom)=g :=
    AffineSchemeAlgebraMap318.spec_hom R N T g (chart_base R A ι S x T f w g h)
  have hx : (VaryingPointIdealNaturality318.mapFree R A ι S T f x).val.val=
      Spec.map (CommRingCat.ofHom γ.toRingHom) ≫ VaryingWordChartGluing318.into R A ι w := by
    rw [hγ]
    exact h
  have hi := VaryingFreePointChartInverse318.right_inverse R A ι T w γ
    (VaryingPointIdealNaturality318.mapFree R A ι S T f x) hx
  have hn := VaryingPointIdealNaturality318.classify_natural R A ι S T f
    (VaryingFreeParameterPoints318.recover R A ι S x)
  have hr := VaryingPointIdealNaturality318.recover_natural R A ι S T f x
  exact congrArg (fun y : VaryingFreeParameterPoints318.FreePoint R A ι T => y.val.val)
    (hn.trans ((congrArg (VaryingFreeParameterPoints318.classify R A ι T) hr.symm).trans hi))
end VaryingFreePointAffineTests318
