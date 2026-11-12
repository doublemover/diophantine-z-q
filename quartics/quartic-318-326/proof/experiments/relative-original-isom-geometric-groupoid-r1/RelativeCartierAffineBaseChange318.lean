module
public import RelativePrincipalChartFamily318
public section
noncomputable section
namespace RelativeCartierAffineBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]
  {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (a : X ⟶ Spec R) [hflat : Flat (p ≫ a)]
  (h : OriginalRegularClosedCharts318.Property p)
include h hflat in
/-- Genuine relative effective Cartier charts survive arbitrary affine
coefficient change when the WHOLE original closed family is flat over
its coefficient base. The new ring may be nonreduced or nonflat over R. -/
lemma regular : OriginalRegularClosedCharts318.Property
    (ClosedFamilyBaseRestriction318.into a p (RelativeOriginalAffineChart318.baseMap R S)) := by
  intro x
  obtain ⟨A,j,hj,hy,c,z,H,hc⟩ := h ((pullback.fst a (RelativeOriginalAffineChart318.baseMap R S)) x)
  letI : IsOpenImmersion j := hj
  let φ : R →+* A := (Spec.preimage (j ≫ a)).hom
  letI : Algebra R A := φ.toAlgebra
  have ha : j ≫ a=Spec.map (CommRingCat.ofHom (algebraMap R A)) :=
    (Spec.map_preimage (j ≫ a)).symm
  letI : Module.Flat R (A ⧸ Ideal.span ({c} : Set A)) :=
    RegularAffineChartFlat318.flat R A p a j ha c z H
  let J := RelativeOriginalAffineChart318.into R S A a j ha
  have hx : x ∈ Set.range J := by
    change x ∈ J.opensRange
    rw [RelativeOriginalAffineChart318.range]
    exact hy
  refine ⟨RelativePrincipalChartEquation318.ring R S A,J,inferInstance,hx,
    RelativePrincipalChartEquation318.equation R S A c,
    RelativePrincipalChartFamily318.into R S A p a j ha c z H,
    RelativePrincipalChartFamily318.cartesian R S A p a j ha c z H,?_⟩
  exact RelativePrincipalChartEquation318.regular R S A c hc
end RelativeCartierAffineBaseChange318
