module
public import CanonicalXScale318
public import ModularTorusTransport318
public import MarkedPeriod318
public section
noncomputable section
namespace CanonicalXModularity318
open UpperHalfPlane OpenJLocalComparison318 ModularCurveChange318
open scoped MatrixGroups
set_option maxHeartbeats 0

lemma source_coefficients (g : GL (Fin 2) ℝ) (hg : g ∈ modularImage) (tau : UpperHalfPlane) :
    A (g•tau:UpperHalfPlane)=A (tau:ℂ) ∧ B (g•tau:UpperHalfPlane)=B (tau:ℂ) := by
  simp only [A,B,j,UpperHalfPlane.ofComplex_apply,ActualJInvariant318.modular_invariant g hg tau]
  exact ⟨trivial,trivial⟩

lemma target_coefficients (g : GL (Fin 2) ℝ) (hg : g ∈ modularImage) (tau : UpperHalfPlane) :
    C (g•tau:UpperHalfPlane)=denom g tau^4*C (tau:ℂ) ∧
    D (g•tau:UpperHalfPlane)=denom g tau^6*D (tau:ℂ) := by
  simp only [C,D,UpperHalfPlane.ofComplex_apply,ModularWeierstrass318.curve,
    NormalizedWeierstrass318.model,E4_transform g hg tau,E6_transform g hg tau]
  constructor <;> ring

/-- The canonical sign-independent x-scale has actual modular weight two. -/
theorem scale_transform (g : GL (Fin 2) ℝ) (hg : g ∈ modularImage) (tau : UpperHalfPlane) :
    CanonicalXScale318.scale (g•tau:UpperHalfPlane)=
      denom g tau^2*CanonicalXScale318.scale (tau:ℂ) := by
  have hA := (source_coefficients g hg tau).1
  have hB := (source_coefficients g hg tau).2
  have hC := (target_coefficients g hg tau).1
  have hD := (target_coefficients g hg tau).2
  simp only [CanonicalXScale318.scale,LocalShortScaling318.ratio,hA,hB,hC,hD]
  rw [show denom g tau^6*D (tau:ℂ)/B (tau:ℂ)=denom g tau^6*(D (tau:ℂ)/B (tau:ℂ))
      from mul_div_assoc _ _ _,
    show denom g tau^4*C (tau:ℂ)/A (tau:ℂ)=denom g tau^4*(C (tau:ℂ)/A (tau:ℂ))
      from mul_div_assoc _ _ _,mul_div_mul_comm]
  congr 1
  field_simp [denom_ne_zero g tau]
  <;> ring

@[expose] def pointX {W : WeierstrassCurve ℂ} : W.toAffine.Point → ℂ
  | .zero => 0
  | .some x _ _ => x

lemma pointX_transport (g : SL(2,ℤ)) (tau : UpperHalfPlane)
    (P : (ModularWeierstrass318.curve tau).toAffine.Point) :
    pointX (ModularTorusTransport318.pointAddEquiv g tau P)=
      denom ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) tau^2*pointX P := by
  cases P with
  | zero =>
      change 0=denom ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) tau^2*0
      simp
  | some x y h => rfl

@[expose] def standardX (tau : UpperHalfPlane) : ℂ := pointX (MarkedPeriod318.standardPoint 3 tau)
@[expose] def arithmeticX (tau : UpperHalfPlane) : ℂ := standardX tau/CanonicalXScale318.scale (tau:ℂ)

lemma standardX_transform (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 3)
    (tau : UpperHalfPlane) :
    standardX (g•tau)=denom ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) tau^2*standardX tau := by
  have hp := (MarkedPeriod318.point_stabilizer 3 g tau).mpr hg
  change pointX (MarkedPeriod318.standardPoint 3 (g•tau))=_
  rw [←hp,pointX_transport]
  rfl

/-- The normalized actual 1/3 torsion coordinate is invariant under the
actual Gamma1(3) source group. This is the coordinate for the specified
arithmetic quartic model, rather than an arbitrary label. -/
theorem arithmeticX_invariant (g : SL(2,ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 3)
    (tau : UpperHalfPlane) : arithmeticX (g•tau)=arithmeticX tau := by
  have hs := scale_transform ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) g) ⟨g,rfl⟩ tau
  change CanonicalXScale318.scale (g•tau:UpperHalfPlane)=_ at hs
  rw [arithmeticX,arithmeticX,standardX_transform g hg tau,hs]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (denom_ne_zero _ tau))

end CanonicalXModularity318
