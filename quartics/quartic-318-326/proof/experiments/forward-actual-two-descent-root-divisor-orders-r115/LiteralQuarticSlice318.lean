module
public import LiteralTernaryReduction318
public section
noncomputable section
namespace LiteralQuarticSlice318
open QuadricCRTAssembly318
set_option maxHeartbeats 1000000

@[expose] def x0 (v : Coordinates ℤ) : ℤ := v.1.1+v.2.1.1
@[expose] def x1 (v : Coordinates ℤ) : ℤ := v.1.1-v.2.1.1
@[expose] def project (v : Coordinates ℤ) : TernaryQuadraticLineCover318.Vector ℤ :=
  (v.1.2-v.2.1.2,v.1.2+v.2.1.2,v.2.2)

/-- Literal original five-coordinate quadric with its UNCHANGED κ. The
parameter2κ is confined to the ternary adapter, never substituted here. -/
theorem factorization (κ : ℤ) (v : Quadric κ) :
    x0 v.1*x1 v.1=LiteralTernaryReduction318.R κ (project v.1) := by
  have h := v.2
  dsimp [equation] at h
  dsimp [x0,x1,project,LiteralTernaryReduction318.R]
  linear_combination h

@[expose] def Slice (κ t : ℤ) (side : Bool) :=
  {v : Quadric κ // (if side then x0 v.1 else x1 v.1)=t}

/-- Each actual slice point satisfies t|R in the same integer coordinates. -/
theorem slice_divides (κ t : ℤ) (side : Bool) (v : Slice κ t side) :
    t∣LiteralTernaryReduction318.R κ (project v.1.1) := by
  rw [←factorization κ v.1]
  have ht := v.2
  cases side with
  | false =>
    change x1 v.1.1=t at ht
    rw [ht]
    exact dvd_mul_left t _
  | true =>
    change x0 v.1.1=t at ht
    rw [ht]
    exact dvd_mul_right t _

/-- The manuscript discards parity ONLY through this injection on a fixed
nonzero slice. No assertion that the full coordinate change is unimodular. -/
theorem slice_projection_injective (κ t : ℤ) (ht : t≠0) (side : Bool) :
    Function.Injective (fun v : Slice κ t side => project v.1.1) := by
  intro v u he
  have hR : x0 v.1.1*x1 v.1.1=x0 u.1.1*x1 u.1.1 := by
    rw [factorization κ v.1,factorization κ u.1,he]
  have hv := v.2
  have hu := u.2
  have h01 : x0 v.1.1=x0 u.1.1 ∧ x1 v.1.1=x1 u.1.1 := by
    cases side with
    | false =>
      change x1 v.1.1=t at hv
      change x1 u.1.1=t at hu
      rw [hv,hu] at hR
      exact ⟨mul_right_cancel₀ ht hR,hv.trans hu.symm⟩
    | true =>
      change x0 v.1.1=t at hv
      change x0 u.1.1=t at hu
      rw [hv,hu] at hR
      exact ⟨hv.trans hu.symm,mul_left_cancel₀ ht hR⟩
  have hx := congrArg Prod.fst he
  have hz := congrArg (fun z : TernaryQuadraticLineCover318.Vector ℤ => z.2.1) he
  have hw := congrArg (fun z : TernaryQuadraticLineCover318.Vector ℤ => z.2.2) he
  obtain ⟨h0,h1⟩ := h01
  dsimp [x0,x1] at h0 h1
  dsimp [project] at hx hz hw
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> linarith
  · apply Prod.ext
    · apply Prod.ext <;> linarith
    · exact hw

/-- Every squarefree modulus dividing the actual slice label imposes the
literal R congruence, without changing any original coefficient or point. -/
theorem slice_modulus_divides (κ t : ℤ) (side : Bool) (v : Slice κ t side)
    (M : ℕ) (hM : (M:ℤ)∣t) :
    (M:ℤ)∣LiteralTernaryReduction318.R κ (project v.1.1) :=
  dvd_trans hM (slice_divides κ t side v)

end LiteralQuarticSlice318
