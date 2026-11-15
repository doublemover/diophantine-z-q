module
public import ActualOriginalSmoothWeight318
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public section
noncomputable section
namespace ActualOriginalPositiveQuadricChart318
open QuadricCRTAssembly318
set_option maxHeartbeats 16000000

@[expose] def Parameters := ℝ×(ℝ×ℝ)×ℝ
@[expose] def projection (x : Coordinates ℝ) : Parameters := (x.1.2,x.2.1,x.2.2)
@[expose] def radicand (κ : ℝ) (v : Parameters) : ℝ :=
  κ*v.2.2^2+v.2.1.1^2+v.2.1.2^2-v.1^2
@[expose] def graph (κ : ℝ) (v : Parameters) : Coordinates ℝ :=
  ((Real.sqrt (radicand κ v),v.1),v.2.1,v.2.2)
@[expose] def Domain (κ : ℝ) := {v : Parameters // 0<radicand κ v}
@[expose] def PositiveQuadric (κ : ℝ) :=
  {x : Coordinates ℝ // equation κ x=0 ∧ 0<x.1.1}

lemma radicand_continuous (κ : ℝ) : Continuous (radicand κ) := by
  unfold radicand
  fun_prop
lemma graph_continuous (κ : ℝ) : Continuous (graph κ) := by
  unfold graph
  fun_prop
lemma projection_continuous : Continuous projection := by unfold projection;fun_prop
lemma projection_graph (κ : ℝ) (v : Parameters) : projection (graph κ v)=v := rfl
lemma graph_on_original (κ : ℝ) (v : Parameters) (hv : 0≤radicand κ v) :
    equation κ (graph κ v)=0 := by
  have hs := Real.sq_sqrt hv
  dsimp [equation,graph,radicand] at *
  nlinarith
lemma original_radicand (κ : ℝ) (x : Coordinates ℝ) (hx : equation κ x=0) :
    radicand κ (projection x)=x.1.1^2 := by
  dsimp [radicand,projection,equation] at *
  nlinarith
lemma graph_projection (κ : ℝ) (x : Coordinates ℝ)
    (hx : equation κ x=0) (ha : 0≤x.1.1) : graph κ (projection x)=x := by
  have he := original_radicand κ x hx
  have hs : Real.sqrt (radicand κ (projection x))=x.1.1 := by rw [he,Real.sqrt_sq ha]
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩,w⟩
  change ((Real.sqrt (radicand κ (projection ((a,b),(c,d),w))),b),(c,d),w)=_
  rw [hs]

/-- The actual positive-a part of the original real quadric is exactly
this four-dimensional square-root graph. -/
@[expose] def actualChart (κ : ℝ) : Domain κ ≃ PositiveQuadric κ where
  toFun v := ⟨graph κ v.1,graph_on_original κ v.1 v.2.le,Real.sqrt_pos.2 v.2⟩
  invFun x := ⟨projection x.1,by
    rw [original_radicand κ x.1 x.2.1]
    exact sq_pos_of_pos x.2.2⟩
  left_inv v := Subtype.ext (projection_graph κ v.1)
  right_inv x := Subtype.ext (graph_projection κ x.1 x.2.1 x.2.2.le)

/-- The derivative is in the original a coordinate, hence the factor is
2a, not a rescaled ternary form or a quotient-map derivative. -/
lemma actual_normal_derivative (κ a b c d w : ℝ) :
    HasDerivAt (fun t : ℝ => equation κ ((t,b),(c,d),w)) (2*a) a := by
  simpa only [equation,pow_one,Nat.cast_ofNat,mul_one] using
    ((((hasDerivAt_id a).pow 2).add_const (b^2)).sub_const (c^2+d^2)).sub_const (κ*w^2)

end ActualOriginalPositiveQuadricChart318
