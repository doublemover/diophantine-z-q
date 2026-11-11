module
public import PELOriginalClopenPrimitiveSheets318
public import LocalizedPrimitiveSelectedGraphs318
public import AnalyticFiniteRootProduct318
public section
noncomputable section
namespace PELOriginalLocalSelectedFactor318
open Set Polynomial
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalClopenPrimitiveSheets318
open AdjoinRootSpecializedPoints318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- A genuine local selected factor for the actual original sheets.
Its roots are exactly the original selected roots in the ENTIRE
independent fiber. Its coefficients are proved analytic and its degree
is one fixed finite cardinal on a common base neighborhood. The empty
selection gives the monic constant one; global positivity, rationality
and equality to the whole candidate polynomial are not assumed. -/
theorem exists_local_selected_factor (hm : Q.Monic) (hs : Q.Separable)
    (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0) :
    ∃ U : Set ComplexVectors, IsOpen U ∧ v ∈ U ∧
    ∃ g : Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv) → ComplexVectors → ℂ,
    ∃ T : Finset (Roots Q (ComplexPolynomialOpenPoints318.evaluation d v hv)),
      (∀ i, g i v = i.val) ∧
      ∀ w ∈ U,
        MvPolynomial.eval w d ≠ 0 ∧
        Function.Injective (fun i => g i w) ∧
        (∀ i, AnalyticAt ℂ (g i) w ∧
          LocalizedPrimitiveRootChart318.equation d Q (w,g i w) = 0) ∧
        (AnalyticFiniteRootProduct318.factor T g w).Monic ∧
        (AnalyticFiniteRootProduct318.factor T g w).natDegree = T.card ∧
        (∀ n, AnalyticAt ℂ
          (fun u => (AnalyticFiniteRootProduct318.factor T g u).coeff n) w) ∧
        ∀ q : OpenRoots d Q, q.val.val.1 = w →
          ((AnalyticFiniteRootProduct318.factor T g w).eval q.val.val.2 = 0 ↔
            q ∈ Set.range (originalOpenRootPoint τ hτ j x d Q e he)) := by
  obtain ⟨U,hU,hUv,g,T,hcenter,hg⟩ :=
    LocalizedPrimitiveSelectedGraphs318.exists_selected_graphs d Q hm hs
      (Set.range (originalOpenRootPoint τ hτ j x d Q e he))
      (selected_open τ hτ j x d Q e he hs) (selected_closed τ hτ j x d Q e he) v hv
  refine ⟨U,hU,hUv,g,T,hcenter,?_⟩
  intro w hw
  have h := hg w hw
  refine ⟨h.1,h.2.2.1,h.2.1,
    AnalyticFiniteRootProduct318.factor_monic T g w,
    AnalyticFiniteRootProduct318.factor_degree T g w,?_,?_⟩
  · intro n
    exact AnalyticFiniteRootProduct318.factor_coeff_analytic T g w
      (fun i _ => (h.2.1 i).1) n
  · intro q hq
    rw [AnalyticFiniteRootProduct318.factor_root]
    exact (h.2.2.2.2 q hq).symm
end PELOriginalLocalSelectedFactor318
