module
public import PELOriginalLocalSelectedFactor318
public import LocalizedPrimitiveSelectedPolynomial318
public section
noncomputable section
namespace PELOriginalGlobalSelectedPolynomial318
open Set Polynomial
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedFiniteOpen318
open PELOriginalRootCoordinates318 PELOriginalClopenPrimitiveSheets318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3) (x : ComplexVectors)
variable (d : BasePolynomial) (Q : Polynomial (Localization.Away d))
variable (e : AdjoinRoot Q ≃+* Localization.Away (polynomialMap τ hτ j x d))
variable (he : ∀ a : Localization.Away d, e (AdjoinRoot.of Q a) =
  Localization.awayMap (polynomialMap τ hτ j x).toRingHom d a)

/-- One actual global selected polynomial, defined by the original
selected points of every independent candidate fiber. -/
@[expose] def selectedPolynomial (hm : Q.Monic) (v : ComplexVectors) : Polynomial ℂ :=
  LocalizedPrimitiveSelectedPolynomial318.selectedPolynomial d Q hm
    (Set.range (originalOpenRootPoint τ hτ j x d Q e he)) v

/-- The original clopen theorem supplies the genuine gluing input for
all global coefficient functions; no local chart choice remains. -/
theorem coefficient_analytic (hm : Q.Monic) (hs : Q.Separable)
    (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0) (n : ℕ) :
    AnalyticAt ℂ (fun w => (selectedPolynomial τ hτ j x d Q e he hm w).coeff n) v :=
  LocalizedPrimitiveSelectedPolynomial318.selected_coeff_analytic d Q hm hs _
    (selected_open τ hτ j x d Q e he hs) (selected_closed τ hτ j x d Q e he) v hv n

lemma selected_monic (hm : Q.Monic) (v : ComplexVectors)
    (hv : MvPolynomial.eval v d ≠ 0) :
    (selectedPolynomial τ hτ j x d Q e he hm v).Monic :=
  LocalizedPrimitiveSelectedPolynomial318.selected_monic d Q hm _ v hv

/-- Literal equality of the selected roots with original sheets, at
every independent root of every candidate fiber on this SAME open. -/
theorem selected_root_iff (hm : Q.Monic) (q : OpenRoots d Q) :
    (selectedPolynomial τ hτ j x d Q e he hm q.val.val.1).eval q.val.val.2 = 0 ↔
      q ∈ Set.range (originalOpenRootPoint τ hτ j x d Q e he) :=
  LocalizedPrimitiveSelectedPolynomial318.selected_root_iff d Q hm _ q

/-- The degree of the SAME globally defined selected polynomial is
locally constant on the base open. Global constancy/positivity requires
the separate connected-base argument, not just this local construction. -/
theorem degree_locally_constant (hm : Q.Monic) (hs : Q.Separable)
    (v : ComplexVectors) (hv : MvPolynomial.eval v d ≠ 0) :
    ∃ U : Set ComplexVectors, IsOpen U ∧ v ∈ U ∧
      ∀ w ∈ U, MvPolynomial.eval w d ≠ 0 ∧
        (selectedPolynomial τ hτ j x d Q e he hm w).natDegree =
          (selectedPolynomial τ hτ j x d Q e he hm v).natDegree := by
  obtain ⟨U,hU,hUv,g,T,hg⟩ :=
    LocalizedPrimitiveSelectedPolynomial318.exists_local_product d Q hm hs _
      (selected_open τ hτ j x d Q e he hs) (selected_closed τ hτ j x d Q e he) v hv
  refine ⟨U,hU,hUv,?_⟩
  intro w hw
  refine ⟨(hg w hw).1,?_⟩
  change (LocalizedPrimitiveSelectedPolynomial318.selectedPolynomial d Q hm _ w).natDegree = _
  rw [(hg w hw).2.2,(hg v hUv).2.2]
  rw [AnalyticFiniteRootProduct318.factor_degree,AnalyticFiniteRootProduct318.factor_degree]
end PELOriginalGlobalSelectedPolynomial318
