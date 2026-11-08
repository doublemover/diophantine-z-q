module
public import ThreeTorsionFieldPoints318
public section
noncomputable section
namespace ThreeTorsionOrderEquiv318
open ThreeTorsionAlgebra318 ThreeTorsionFunctor318
set_option maxHeartbeats 0
variable {R K : Type*} [CommRing R] [Field K] [DecidableEq K] [Algebra R K]
  (A B : R) [Invertible (3:R)] (hD : IsUnit (-16*(4*A^3+27*B^2)))

abbrev Curve := ThreeTorsionPoints318.curve (algebraMap R K A) (algebraMap R K B)
abbrev OrderThree := {P : (Curve (K:=K) A B).toAffine.Point // addOrderOf P=3}

@[expose] def toPoint (p : Solutions (S:=K) A B) : OrderThree (K:=K) A B :=
  let hp := (ThreeTorsionFieldPoints318.solution_iff_order_three A B hD p.val.1 p.val.2).mp p.property
  ⟨.some p.val.1 p.val.2 hp.choose, hp.choose_spec⟩

@[expose] def toSolution (p : OrderThree (K:=K) A B) : Solutions (S:=K) A B :=
  match p with
  | ⟨.zero, hp⟩ => False.elim (by
      change addOrderOf (0 : (Curve (K:=K) A B).toAffine.Point)=3 at hp
      simpa using hp)
  | ⟨.some x y hx, hp⟩ => ⟨(x,y),
      (ThreeTorsionFieldPoints318.solution_iff_order_three A B hD x y).mpr ⟨hx,hp⟩⟩

/-- The actual finite solutions are in bijection with nonzero order-three
points, including the exclusion of the identity. -/
@[expose] def solutionPointEquiv : Solutions (S:=K) A B ≃ OrderThree (K:=K) A B where
  toFun := toPoint A B hD
  invFun := toSolution A B hD
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by
    obtain ⟨P,hP⟩ := p
    cases P with
    | zero => exact False.elim (by
        change addOrderOf (0 : (Curve (K:=K) A B).toAffine.Point)=3 at hP
        simpa using hP)
    | some x y hx => apply Subtype.ext; rfl

/-- The literal rank-eight algebra represents actual exact-order-three field
points, not only polynomial roots or a cardinality match. -/
@[expose] def algebraPointEquiv : (Ring A B hD →ₐ[R] K) ≃ OrderThree (K:=K) A B :=
  (ThreeTorsionFunctor318.solutionEquiv A B hD).trans (solutionPointEquiv A B hD)

end ThreeTorsionOrderEquiv318
