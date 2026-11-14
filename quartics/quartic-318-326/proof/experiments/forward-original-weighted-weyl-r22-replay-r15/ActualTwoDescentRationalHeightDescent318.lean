module
public import ActualTwoDescentFourQuotientPointConsumer318
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.EllipticCurve
public import Mathlib.GroupTheory.Index
public section
noncomputable section
namespace ActualTwoDescentRationalHeightDescent318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticDoubleQuotient318
open WeierstrassCurve.Affine (approx_parallelogram_law)

/-- The actual original rational curve has a finite-index doubling image
whenever its already-constructed actual quotient is finite. -/
lemma actual_doubles_finite_index (n : ℚ) (hf : Finite (DoubleQuotient n)) :
    (powMonoidHom (α:=Multiplicative (Point n)) 2).range.FiniteIndex := by
  letI := hf
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Genuine Mordell-Weil finite generation from the actual finite doubling
quotient and pinned number-field Northcott/elliptic height descent. -/
theorem actual_finite_generation (n : ℚ) (hn : n ≠ 0) (hf : Finite (DoubleQuotient n)) :
    AddGroup.FG (Point n) := by
  letI : (curve n).toAffine.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (curve_discriminant_ne n hn)⟩
  obtain ⟨C,hC⟩ := approx_parallelogram_law (curve n).toAffine
  letI : Northcott (fun P : Multiplicative (Point n) => P.toAdd.naiveHeight) := {
    finite_le := fun B => (WeierstrassCurve.Affine.finite_naiveHeight_le (curve n).toAffine B).preimage
      (f:=fun P : Multiplicative (Point n) => P.toAdd) Multiplicative.toAdd.injective.injOn }
  apply AddGroup.fg_iff_mul_fg.mpr
  exact CommGroup.fg_of_descent' (h:=fun P : Multiplicative (Point n) => P.toAdd.naiveHeight)
    (actual_doubles_finite_index n hf)
    (fun P => by rw [P.toAdd.naiveHeight_eq_logHeight]; exact Height.logHeight_nonneg _)
    (fun P Q => hC P.toAdd Q.toAdd)

/-- Finiteness of actual rational torsion is a height theorem, independently
of a rank-one assumption or identification of the torsion subgroup. -/
theorem actual_rational_torsion_finite (n : ℚ) (hn : n ≠ 0) :
    Finite (AddCommGroup.torsion (Point n)) := by
  letI : (curve n).toAffine.IsElliptic := ⟨isUnit_iff_ne_zero.mpr (curve_discriminant_ne n hn)⟩
  exact WeierstrassCurve.Affine.finite_torsion

end ActualTwoDescentRationalHeightDescent318
