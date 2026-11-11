module
public import PELHeightCompactSublevels318
public section
noncomputable section
namespace PELOriginalOrbitHeightMinimum318
open QuaternionicJointPeriodTopology318 PELDirichletHeight318 PELHeightCompactSublevels318
open PELJointNormOneAction318 PELNormOneBaseAction318
set_option maxHeartbeats 1600000

/-- Proper discontinuity of the ACTUAL original norm-one group makes the
bounded-height orbit search finite. No finite-index or fundamental-domain premise. -/
theorem bounded_movers_finite (τ : HalfPlane) :
    Set.Finite {u : normOneUnits | height (u • τ)≤height τ} := by
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ:=normOneUnits) (isCompact_singleton (x:=τ))
    (sublevel_compact (height τ) (height_pos τ))
  apply hf.subset
  intro u hu
  exact ⟨u • τ,⟨τ,by simp,rfl⟩,hu⟩

/-- Every original orbit has an actual minimum-height representative.
This is derived from finite bounded movers, not assumed reduction theory. -/
theorem original_minimum (τ : HalfPlane) :
    ∃ u : normOneUnits, ∀ v : normOneUnits,
      height (u • τ)≤height (v • (u • τ)) := by
  let G : Set normOneUnits := {u | height (u • τ)≤height τ}
  have hG : G.Finite := bounded_movers_finite τ
  have hone : (1:normOneUnits)∈G := by simp [G]
  have hne : ((fun u : normOneUnits => u • τ) '' G).Nonempty :=
    ⟨τ,1,hone,one_smul _ _⟩
  obtain ⟨σ,⟨u,hu,rfl⟩,hmin⟩ :=
    (hG.image (fun u : normOneUnits => u • τ)).isCompact.exists_isMinOn hne
      height_continuous.continuousOn
  refine ⟨u,fun v => ?_⟩
  by_cases hv : height (v • (u • τ))≤height τ
  · apply hmin
    refine ⟨v*u,?_,mul_smul v u τ⟩
    simpa only [G,mul_smul,Set.mem_setOf_eq] using hv
  · exact hu.trans (le_of_lt (lt_of_not_ge hv))
end PELOriginalOrbitHeightMinimum318
