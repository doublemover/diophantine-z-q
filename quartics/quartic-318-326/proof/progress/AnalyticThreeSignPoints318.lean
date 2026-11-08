module
public import LiteralThreeXComparison318
public section
noncomputable section
namespace AnalyticThreeSignPoints318
open LiteralThreeXComparison318
set_option maxHeartbeats 0

abbrev Curve (tau : UpperHalfPlane) := ModularWeierstrass318.curve tau
abbrev Points (tau : UpperHalfPlane) := {P : (Curve tau).toAffine.Point // addOrderOf P=3}

lemma short_curve (tau : UpperHalfPlane) :
    ThreeTorsionPoints318.curve (Curve tau).a₄ (Curve tau).a₆ = Curve tau := rfl

lemma discriminant_unit (tau : UpperHalfPlane) :
    IsUnit (-16*(4*(Curve tau).a₄^3+27*(Curve tau).a₆^2)) := by
  rw [←TwoTorsionPoints318.discriminant]
  change IsUnit (Curve tau).Δ
  exact (Curve tau).isUnit_Δ

/-- The analytic quartic roots are exactly x-coordinates of actual
nonzero order-three points on the genuine Eisenstein curve. -/
theorem root_iff (tau : UpperHalfPlane) (x : ℂ) :
    (ThreeTorsionIdentity318.divisionPolynomial (Curve tau).a₄ (Curve tau).a₆).eval x=0 ↔
      ∃ y, ∃ hn : (Curve tau).toAffine.Nonsingular x y,
        addOrderOf (WeierstrassCurve.Affine.Point.some x y hn)=3 := by
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := IsSepClosed.exists_pow_nat_eq
      (x^3+(Curve tau).a₄*x+(Curve tau).a₆) 2
    have he : (Curve tau).toAffine.Equation x y := by
      simpa [WeierstrassCurve.Affine.equation_iff,Curve,ModularWeierstrass318.curve,
        NormalizedWeierstrass318.model] using hy
    have hn := ((Curve tau).toAffine.equation_iff_nonsingular_of_Δ_ne_zero
      (ModularWeierstrass318.curve_discriminant_ne_zero tau)).mp he
    exact ⟨y,hn,(ThreeTorsionPoints318.root_iff_order_three _ _ (discriminant_unit tau) hn).mp hx⟩
  · rintro ⟨y,hn,ho⟩
    exact (ThreeTorsionPoints318.root_iff_order_three _ _ (discriminant_unit tau) hn).mpr ho

@[expose] def toRoot (tau : UpperHalfPlane) (P : Points tau) : AnalyticRoots tau :=
  match P with
  | ⟨.zero,ho⟩ => False.elim (by
      change addOrderOf (0 : (Curve tau).toAffine.Point)=3 at ho
      simpa using ho)
  | ⟨.some x y hn,ho⟩ => ⟨x,(root_iff tau x).mpr ⟨y,hn,ho⟩⟩

lemma toRoot_surjective (tau : UpperHalfPlane) : Function.Surjective (toRoot tau) := by
  intro r
  obtain ⟨y,hn,ho⟩ := (root_iff tau r.val).mp r.property
  exact ⟨⟨.some r.val y hn,ho⟩,rfl⟩

/-- Exactly the genuine elliptic sign relation, with no arbitrary labeling. -/
lemma toRoot_eq_iff (tau : UpperHalfPlane) (P Q : Points tau) :
    toRoot tau P=toRoot tau Q ↔ P.val=Q.val ∨ P.val=-Q.val := by
  obtain ⟨P,hP⟩ := P
  obtain ⟨Q,hQ⟩ := Q
  cases P with
  | zero =>
    change addOrderOf (0 : (Curve tau).toAffine.Point)=3 at hP
    simp at hP
  | some x₁ y₁ hn₁ =>
    cases Q with
    | zero =>
      change addOrderOf (0 : (Curve tau).toAffine.Point)=3 at hQ
      simp at hQ
    | some x₂ y₂ hn₂ =>
      simp only [toRoot,Subtype.mk.injEq]
      exact WeierstrassCurve.Affine.Point.X_eq_iff

@[expose] def signSetoid (tau : UpperHalfPlane) : Setoid (Points tau) := Setoid.ker (toRoot tau)
abbrev SignPoints (tau : UpperHalfPlane) := Quotient (signSetoid tau)

lemma sign_relation (tau : UpperHalfPlane) (P Q : Points tau) :
    (signSetoid tau).r P Q ↔ P.val=Q.val ∨ P.val=-Q.val := toRoot_eq_iff tau P Q

@[expose] def quotientRoot (tau : UpperHalfPlane) : SignPoints tau → AnalyticRoots tau :=
  Quotient.lift (toRoot tau) (fun _ _ h => h)

/-- Actual exact-order-three points modulo elliptic negation are canonically
the actual analytic third-division quartic roots. -/
@[expose] def signRootEquiv (tau : UpperHalfPlane) : SignPoints tau ≃ AnalyticRoots tau :=
  Equiv.ofBijective (quotientRoot tau) ⟨by
    intro P Q he
    induction P using Quotient.inductionOn with
    | h P =>
      induction Q using Quotient.inductionOn with
      | h Q => exact Quotient.sound he,
    by
      intro r
      obtain ⟨P,hP⟩ := toRoot_surjective tau r
      exact ⟨Quotient.mk _ P,hP⟩⟩

/-- The full diamond fixed algebra of the specified arithmetic family now
has a canonical complex-point comparison with actual analytic order-three
points modulo sign. A global modular-curve identification is not asserted. -/
@[expose] def fixedSignEquiv (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : OpenJComplexEvaluation318.Admissible tau) :
    letI : Algebra (OpenJModel318.Base N) ℂ := (OpenJComplexEvaluation318.evaluation N tau h).toAlgebra
    (LiteralThreeXComparison318.Fixed N →ₐ[OpenJModel318.Base N] ℂ) ≃ SignPoints tau := by
  letI : Algebra (OpenJModel318.Base N) ℂ := (OpenJComplexEvaluation318.evaluation N tau h).toAlgebra
  exact (LiteralThreeXComparison318.fixedRootEquiv N tau h).trans (signRootEquiv tau).symm

end AnalyticThreeSignPoints318
