module
public import ActualOriginalFiniteCoverIntegral318
public section
noncomputable section
namespace ActualOriginalMinorRationalIntegral318
open QuadricCRTAssembly318 ActualOriginalScaledCircle318 ActualOriginalCompactCircleCount318
open ActualOriginalMajorArcDomain318 ActualOriginalCircleMinorArcIdentity318
open ActualOriginalMinorDirichlet318 ActualOriginalMinorRationalCells318
open ActualOriginalRationalCellIntegral318 ActualOriginalFiniteCoverIntegral318 MeasureTheory
open scoped BigOperators ContDiff

/-- An actual integrated bound with produced smooth constants, produced
Dirichlet approximants, the actual minor-domain cover, and all numerator
multiplicities retained. It is NOT yet a power-saving estimate. -/
theorem actual_minor_rational_integral (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R C : ℝ, 1≤R ∧ 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ N : ℕ, 0<N →
      ((N : ℝ)+1)^3≤B → ∀ Q : ℕ, 0<Q → 1/((Q : ℝ)+1)<radius N B →
      ‖minorArcIntegral κ N B W‖≤∑ i∈rationalIndices N Q,
        rationalWeylEnvelope κ R C B i.1*(2*dirichletWidth Q i.1) := by
  obtain ⟨R,C,hR,hC,hcell⟩ := actual_rational_cell_bounds κ hκ W hW hc
  refine ⟨R,C,hR,hC,fun B hB N hN hs Q hQ hw => ?_⟩
  have hBp : 0<B := by linarith
  have hct := actual_scaled_circle_continuous κ B hBp.ne' W hc
  have hi : IntegrableOn (fun t => scaledCircleSum κ t B W) (minorDomain N B) :=
    (hct.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).mono_set Set.diff_subset
  have hb := actual_finite_cover_integral (rationalIndices N Q) (minorDomain N B)
    (minor_measurable N B) (fun i => minorCell N Q B i.2 i.1)
    (fun i _ => actual_minor_cell_measurable N Q B i.2 i.1)
    (fun _ _ => Set.inter_subset_left)
    (actual_minor_rational_cover N hN B hBp hs Q hQ hw)
    (fun t => scaledCircleSum κ t B W) hi
  apply hb.trans
  apply Finset.sum_le_sum
  intro i hi'
  simp only [rationalIndices,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc] at hi'
  exact (hcell B hB N Q i.2 i.1 (by omega) hi'.1.1.2 hi'.2.2).2

/-- The integration theorem is nonvacuous at the explicit order ceil(B²/N).
No existential Diophantine input remains for the caller to supply. -/
theorem actual_minor_rational_integral_canonical (κ : ℤ) (hκ : κ≠0)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R C : ℝ, 1≤R ∧ 0≤C ∧ ∀ B : ℝ, 1≤B → ∀ N : ℕ, 0<N →
      ((N : ℝ)+1)^3≤B →
      ‖minorArcIntegral κ N B W‖≤∑ i∈rationalIndices N ⌈B^2/(N : ℝ)⌉₊,
        rationalWeylEnvelope κ R C B i.1*(2*dirichletWidth ⌈B^2/(N : ℝ)⌉₊ i.1) := by
  obtain ⟨R,C,hR,hC,hb⟩ := actual_minor_rational_integral κ hκ W hW hc
  refine ⟨R,C,hR,hC,fun B hB N hN hs => ?_⟩
  have ho := actual_minor_dirichlet_order N hN B (by linarith)
  exact hb B hB N hN hs _ ho.1 ho.2

end ActualOriginalMinorRationalIntegral318
