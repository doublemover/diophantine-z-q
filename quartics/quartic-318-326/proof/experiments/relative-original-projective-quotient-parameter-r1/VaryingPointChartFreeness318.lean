module
public import VaryingFreePointChartInverse318
public import AffineSchemeAlgebraMap318
public section
noncomputable section
namespace VaryingPointChartFreeness318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingParameterPoint318.Point R A ι S) (w : ι → List A)
local notation "N" => VaryingNormalizedWordParameter318.ring R A ι w
variable (g : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of N))
  (h : x.val=g ≫ VaryingWordChartGluing318.into R A ι w)
include h
lemma chart_base : g ≫ VaryingSourceCoefficientPullback318.base R N=
    VaryingSourceCoefficientPullback318.base R S := by
  rw [← VaryingWordParameterStructure318.into_structureMap R A ι w,← Category.assoc,← h]
  exact x.property
/-- Freeness on an actual parameter chart is proved from its genuine
normalized quotient producer. It is NOT assumed for arbitrary points. -/
lemma free : Nonempty (Module.Basis ι S ((S ⊗[R] A) ⧸
    VaryingParameterPointIdeal318.ideal R A ι S x)) := by
  let γ := AffineSchemeAlgebraMap318.hom R N S g (chart_base R A ι S x w g h)
  let I := VaryingFreePointChartInverse318.ideal R A ι S w γ
  have hg : Spec.map (CommRingCat.ofHom γ.toRingHom)=g :=
    AffineSchemeAlgebraMap318.spec_hom R N S g (chart_base R A ι S x w g h)
  have hx : VaryingParameterPoint318.ofIdeal R A ι S I=x := by
    apply Subtype.ext
    exact (VaryingFreePointChartInverse318.classify_ideal R A ι S w γ).trans
      ((congrArg (fun k => k ≫ VaryingWordChartGluing318.into R A ι w) hg).trans h.symm)
  rw [← hx,VaryingClassifiedIdealRecovery318.ideal_ofIdeal]
  exact I.property
end VaryingPointChartFreeness318
