module
public import CanonicalQuadratic
public import BasePointHeight318
public import GlobalDuplicationHeight318
public import Mathlib.NumberTheory.Height.EllipticCurve
public section
noncomputable section
open ConcreteG8Domain LocalGenerator318 GlobalSaturationHeight318
open WeierstrassCurve.Affine Filter Topology
namespace ActualCanonicalHeight318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def canonicalHeight (P:E.Point) : ℝ := CanonicalLimit.height xHeight P

lemma actual_bounds : CanonicalLimit.Bounds xHeight (Real.log 392) (Real.log 676) := by
  refine ⟨Real.log_nonneg (by norm_num),Real.log_nonneg (by norm_num),?_,?_⟩
  · intro P
    rw [←natCast_zsmul]
    exact (GlobalDuplicationHeight318.absolute_duplication_bounds P).1
  · intro P
    rw [←natCast_zsmul]
    exact (GlobalDuplicationHeight318.absolute_duplication_bounds P).2

lemma naiveHeight_eq_twice (P:E.Point) : P.naiveHeight=2*xHeight P := by
  rw [Point.naiveHeight_eq_logHeight,GlobalDuplicationHeight318.absolute_height_eq_half_relative]
  simp only [RelativeDuplicationHeight318.relativeXHeight]
  ring

lemma actual_parallelogram :
    ∃C:ℝ,∀P Q:E.Point,|xHeight (P+Q)+xHeight (P-Q)-2*(xHeight P+xHeight Q)|≤C := by
  classical
  let : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr RootPointAlgebra318.discriminant_nonzero⟩
  obtain ⟨C,hC⟩ := WeierstrassCurve.Affine.approx_parallelogram_law E
  refine ⟨C/2,fun P Q => ?_⟩
  have hh := hC P Q
  simp only [naiveHeight_eq_twice] at hh
  have he : 2*xHeight (P+Q)+2*xHeight (P-Q)-2*(2*xHeight P+2*xHeight Q)=
      2*(xHeight (P+Q)+xHeight (P-Q)-2*(xHeight P+xHeight Q)) := by ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  linarith

lemma actual_zero : xHeight (0:E.Point)=0 := by
  rw [GlobalDuplicationHeight318.absolute_height_eq_half_relative]
  simp [RelativeDuplicationHeight318.relativeXHeight,Point.xRep]

lemma actual_nonneg (P:E.Point) : 0≤xHeight P := by
  rw [GlobalDuplicationHeight318.absolute_height_eq_half_relative]
  exact div_nonneg (Height.logHeight_nonneg _) (by norm_num)

/-- This is the genuine Tate doubling limit in the exact source normalization. -/
theorem canonical_tendsto (P:E.Point) :
    Tendsto (fun n:ℕ => (1/4:ℝ)^n*xHeight ((2^n:ℕ) • P)/2)
      atTop (𝓝 (canonicalHeight P)) := by
  exact (CanonicalLimit.tendsto_raw actual_bounds P).div_const 2

/-- Every field of the live canonical-height interface is proved here,
including integer quadraticity, actual 2-torsion invariance and base height. -/
theorem canonical_data : CanonicalData canonicalHeight := by
  obtain ⟨C,hC⟩ := actual_parallelogram
  constructor
  · simp only [canonicalHeight,CanonicalLimit.height,CanonicalLimit.raw_zero actual_bounds actual_zero,zero_div]
  · intro P
    exact div_nonneg (CanonicalLimit.raw_nonneg actual_bounds actual_nonneg P) (by norm_num)
  · intro n P
    change CanonicalLimit.raw xHeight (n • P)/2=(n:ℝ)^2*(CanonicalLimit.raw xHeight P/2)
    rw [CanonicalQuadratic.raw_zsmul actual_bounds actual_zero hC]
    ring
  · intro P T hT
    change CanonicalLimit.raw xHeight (P+T)/2=CanonicalLimit.raw xHeight P/2
    rw [CanonicalLimit.raw_two_torsion actual_bounds P T hT]
  · intro P
    have hh := (CanonicalLimit.raw_bounds actual_bounds P).1
    change xHeight P≤2*(CanonicalLimit.raw xHeight P/2)+Real.log 392/3
    linarith
  · intro P
    have hh := (CanonicalLimit.raw_bounds actual_bounds P).2
    change 2*(CanonicalLimit.raw xHeight P/2)≤xHeight P+Real.log 676/3
    linarith
  · exact BasePointHeight318.heightP

#print axioms actual_bounds
#print axioms naiveHeight_eq_twice
#print axioms actual_parallelogram
#print axioms actual_zero
#print axioms actual_nonneg
#print axioms canonical_tendsto
#print axioms canonical_data
end ActualCanonicalHeight318
