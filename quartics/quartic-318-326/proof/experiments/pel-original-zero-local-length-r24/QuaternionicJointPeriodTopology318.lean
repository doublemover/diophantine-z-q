module
public import PELComplexPeriodSurface318
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public section
noncomputable section
namespace QuaternionicJointPeriodTopology318
open QuaternionicRealPeriod318
set_option maxHeartbeats 1200000
abbrev HalfPlane := {τ : ℂ // 0<τ.im}
abbrev Cover := HalfPlane × ComplexVectors
@[expose] def basePoint : HalfPlane := ⟨Complex.I,by simp⟩
instance : Inhabited HalfPlane := ⟨basePoint⟩

/-- Joint continuity is proved in both the parameter and the vector. It is
not inferred from the continuity of each separate period isomorphism. -/
theorem continuous_period : Continuous (fun p : ℂ × RealMatrices => period p.1 p.2) := by
  apply continuous_pi
  intro i
  change Continuous (fun p : ℂ × RealMatrices => (p.2 i 0:ℂ)*p.1+(p.2 i 1:ℂ))
  fun_prop

@[expose] def inverseMatrix (τ : HalfPlane) (z : ComplexVectors) : RealMatrices :=
  fun i => inverseRow τ (z i)

theorem inverseMatrix_eq (τ : HalfPlane) (z : ComplexVectors) :
    inverseMatrix τ z=(periodEquiv τ τ.property).symm z := rfl

theorem continuous_inverseMatrix :
    Continuous (fun p : Cover => inverseMatrix p.1 p.2) := by
  have ht : Continuous (fun p : Cover => (p.1:ℂ).im) := by fun_prop
  have hr : Continuous (fun p : Cover => (p.1:ℂ).re) := by fun_prop
  have hi (i : Fin 2) : Continuous (fun p : Cover => (p.2 i).im/(p.1:ℂ).im) :=
    (by fun_prop : Continuous (fun p : Cover => (p.2 i).im)).div ht
      (fun p => p.1.property.ne')
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases j
  · change Continuous (fun p : Cover => (p.2 i).im/(p.1:ℂ).im)
    exact hi i
  · change Continuous (fun p : Cover => (p.2 i).re-
      ((p.2 i).im/(p.1:ℂ).im)*(p.1:ℂ).re)
    exact (by fun_prop : Continuous (fun p : Cover => (p.2 i).re)).sub ((hi i).mul hr)

@[expose] def fixedPeriod : RealMatrices ≃ₗ[ℝ] ComplexVectors :=
  periodEquiv basePoint basePoint.property

/-- The joint real trivialization sends fixed-reference periods to actual
periods at τ. This is a homeomorphism, not a holomorphic trivialization. -/
@[expose] def realTrivialization : Cover ≃ₜ Cover where
  toFun p := (p.1,period p.1 (fixedPeriod.symm p.2))
  invFun p := (p.1,fixedPeriod (inverseMatrix p.1 p.2))
  left_inv p := by
    change (p.1,fixedPeriod (inverseMatrix p.1 (period p.1 (fixedPeriod.symm p.2))))=p
    apply Prod.ext
    · rfl
    · change fixedPeriod ((periodEquiv p.1 p.1.property).symm
        (periodEquiv p.1 p.1.property (fixedPeriod.symm p.2)))=p.2
      rw [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]
  right_inv p := by
    change (p.1,period p.1 (fixedPeriod.symm (fixedPeriod (inverseMatrix p.1 p.2))))=p
    apply Prod.ext
    · rfl
    · change periodEquiv p.1 p.1.property (fixedPeriod.symm
        (fixedPeriod ((periodEquiv p.1 p.1.property).symm p.2)))=p.2
      rw [LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]
  continuous_toFun := by
    apply continuous_fst.prodMk
    exact continuous_period.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (fixedPeriod.symm.toLinearMap.toContinuousLinearMap.continuous.comp continuous_snd))
  continuous_invFun := by
    apply continuous_fst.prodMk
    exact fixedPeriod.toLinearMap.toContinuousLinearMap.continuous.comp continuous_inverseMatrix

@[expose] def referenceMap (τ : HalfPlane) : ComplexVectors ≃ₗ[ℝ] ComplexVectors :=
  (periodEquiv τ τ.property).symm.trans fixedPeriod

theorem referenceMap_period (τ : HalfPlane) (M : RealMatrices) :
    referenceMap τ (period τ M)=period basePoint M := by
  change fixedPeriod ((periodEquiv τ τ.property).symm (periodEquiv τ τ.property M))=_
  rw [LinearEquiv.symm_apply_apply]
  all_goals rfl
end QuaternionicJointPeriodTopology318
