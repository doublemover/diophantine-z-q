module
public import SelectedActualPrimitiveOrbit318
public import SelectedMarkedPeriodCoordinate318
public section
noncomputable section
open scoped MatrixGroups
namespace SelectedActualPeriodFiber318

open OpenJComplexEvaluation318 UpperHalfPlane
open CanonicalXModularity318 ModularCurveChange318

theorem coefficient_j_transform (g : SL(2,ℤ)) (τ : UpperHalfPlane) :
    ActualQJ318.jInvariant (g • τ) = ActualQJ318.jInvariant τ :=
  ActualJInvariant318.modular_invariant
    ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) g) ⟨g,rfl⟩ τ

theorem admissible_transform (g : SL(2,ℤ)) (τ : UpperHalfPlane) (h : Admissible τ) :
    Admissible (g • τ) := by
  simpa only [Admissible,coefficient_j_transform] using h

/-- The x of an arbitrary genuine point of the actual evaluated short
model scales by exactly the sign-independent comparison factor. -/
theorem scaled_x (N : ℕ) [NeZero N] (τ : UpperHalfPlane) (h : Admissible τ)
    (P : (fiber N τ h).toAffine.Point) :
    pointX (OpenJAnalyticPoints318.pointAddEquiv N τ h P) =
      CanonicalXScale318.scale (τ : ℂ) * pointX P := by
  let s := OpenJAnalyticPoints318.scaling N τ h
  have hs := OpenJAnalyticPoints318.scaling_spec N τ h
  rw [CanonicalXScale318.scale_eq_square N τ h s hs.1 hs.2]
  change pointX (ShortScaling318.pointMap _ _ s hs.1 hs.2 P) =
    (s : ℂ)^2 * pointX P
  cases P with
  | zero => simp [pointX,ShortScaling318.pointMap]
  | some x y hxy => rfl

/-- All exact-order abscissas over this actual ordinary j are attained,
with no need to choose a sign or match chart points by equal counts. -/
theorem every_fiber_mark (N : ℕ) [NeZero N] (τ : UpperHalfPlane) (h : Admissible τ)
    (P : (fiber N τ h).toAffine.Point) (hP : addOrderOf P = N) :
    ∃ g : SL(2,ℤ),
      Admissible (g • τ) ∧
      ActualQJ318.jInvariant (g • τ) = ActualQJ318.jInvariant τ ∧
      SelectedMarkedPeriodCoordinate318.arithmeticX N (g • τ) = pointX P := by
  let Q := OpenJAnalyticPoints318.pointAddEquiv N τ h P
  have hQ : addOrderOf Q = N :=
    (OpenJAnalyticPoints318.pointAddEquiv_order N τ h P).trans hP
  obtain ⟨g,hg⟩ := SelectedActualPrimitiveOrbit318.exists_point_transport N τ Q hQ
  have hx := congrArg (fun R => pointX R) hg
  rw [pointX_transport] at hx
  have hs := scale_transform ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) g) ⟨g,rfl⟩ τ
  change CanonicalXScale318.scale (g • τ : UpperHalfPlane) = _ at hs
  have hd := UpperHalfPlane.denom_ne_zero
    ((Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ) g) τ
  refine ⟨g,admissible_transform g τ h,coefficient_j_transform g τ,?_⟩
  change pointX (MarkedPeriod318.standardPoint N (g • τ)) /
    CanonicalXScale318.scale (g • τ : UpperHalfPlane) = pointX P
  rw [←hx,hs,mul_div_mul_left _ _ (pow_ne_zero 2 hd)]
  apply (div_eq_iff (CanonicalXScale318.scale_ne_zero N τ h)).mpr
  exact (scaled_x N τ h P).trans (mul_comm _ _)

end SelectedActualPeriodFiber318

#print axioms SelectedActualPeriodFiber318.scaled_x
#print axioms SelectedActualPeriodFiber318.every_fiber_mark
