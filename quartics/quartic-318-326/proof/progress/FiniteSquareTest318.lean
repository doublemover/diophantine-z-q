module
public import LocalGenerator318
public import Mathlib.Data.Rat.Sqrt
public section
namespace FiniteSquareTest318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A computable necessary and sufficient square test over Q(sqrt 2). -/
@[expose] def SquareTest (u v : ℚ) : Prop :=
  if v=0 then IsSquare u ∨ IsSquare (u/2)
  else IsSquare (u^2-2*v^2) ∧
    (IsSquare ((u+Rat.sqrt (u^2-2*v^2))/2) ∨
     IsSquare ((u-Rat.sqrt (u^2-2*v^2))/2))
instance (u v:ℚ) : Decidable (SquareTest u v) := by unfold SquareTest; infer_instance

/-- The zero real-part branch is retained, so this test does not divide by
an unchecked square-root coordinate. -/
theorem square_test_of_square (u v : ℚ) (y : K) (hy:y^2=pair u v) : SquareTest u v := by
  have hu : y.re^2+2*y.im^2=u := by
    have he := congrArg QuadraticAlgebra.re hy
    simp [pair,pow_two] at he
    nlinarith [he]
  have hv : 2*y.re*y.im=v := by
    have he := congrArg QuadraticAlgebra.im hy
    simp [pair,pow_two] at he
    nlinarith [he]
  unfold SquareTest
  split_ifs with hzero
  · have hz : y.re=0 ∨ y.im=0 := by
      have : y.re*y.im=0 := by linarith [hv]
      exact mul_eq_zero.mp this
    rcases hz with hr|hi
    · right; refine ⟨y.im,?_⟩; rw [hr] at hu; nlinarith
    · left; refine ⟨y.re,?_⟩; rw [hi] at hu; nlinarith
  · have hn : u^2-2*v^2=(y.re^2-2*y.im^2)^2 := by rw [←hu,←hv]; ring
    refine ⟨⟨y.re^2-2*y.im^2,by rw [hn]; ring⟩,?_⟩
    have hs : Rat.sqrt (u^2-2*v^2)=|y.re^2-2*y.im^2| := by
      rw [hn,pow_two,Rat.sqrt_eq]
    rw [hs]
    rcases le_total 0 (y.re^2-2*y.im^2) with hp|hm
    · left; rw [abs_of_nonneg hp]; refine ⟨y.re,?_⟩; linarith [hu]
    · right; rw [abs_of_nonpos hm]; refine ⟨y.re,?_⟩; linarith [hu]

@[expose] def rhsReal (u v:ℚ) : ℚ := u^3+6*u*v^2-11*u+12*v
@[expose] def rhsImag (u v:ℚ) : ℚ := 3*u^2*v+2*v^3-11*v+6*u
@[expose] def CurveTest (u v:ℚ) : Prop := SquareTest (rhsReal u v) (rhsImag u v)
instance (u v:ℚ) : Decidable (CurveTest u v) := by unfold CurveTest; infer_instance

theorem curve_test_of_equation (u v:ℚ) (y:K) (hy:E.Equation (pair u v) y) :
    CurveTest u v := by
  have he : y^2=pair (rhsReal u v) (rhsImag u v) := by
    rw [equation_iff] at hy
    have hy' : y^2=(pair u v)^3-D*(pair u v) := by simpa [E,sub_eq_add_neg] using hy
    rw [hy']; ext <;> simp [rhsReal,rhsImag,pair,D,i,pow_succ] <;> ring
  exact square_test_of_square _ _ y he

@[expose] def Survivor (u v:ℚ) : Prop :=
  (u=0 ∧ v=0) ∨ (u=3 ∧ v= -1) ∨ (u= -3 ∧ v=1) ∨
  (u=1 ∧ v=1) ∨ (u=23 ∧ v= -17) ∨ (u=2 ∧ v=4) ∨ (u=5/2 ∧ v= -2)
instance (u v:ℚ) : Decidable (Survivor u v) := by unfold Survivor; infer_instance

@[expose] def PrimitiveCandidate (a:ℕ) (b:ℤ) (k:ℕ) : Prop :=
  let num : ℤ := b^2-2*(k:ℤ)^2
  let c : ℤ := num/(4*(a:ℤ))
  num % (4*(a:ℤ))=0 ∧ c.natAbs≤81 ∧ Nat.gcd (Nat.gcd a b.natAbs) c.natAbs=1
instance (a:ℕ) (b:ℤ) (k:ℕ) : Decidable (PrimitiveCandidate a b k) := by
  unfold PrimitiveCandidate; infer_instance

@[expose] def CheckCandidate (a:ℕ) (b:ℤ) (k:ℕ) : Prop :=
  PrimitiveCandidate a b k →
    (CurveTest (-(b:ℚ)/(2*a)) ((k:ℚ)/(2*a)) → Survivor (-(b:ℚ)/(2*a)) ((k:ℚ)/(2*a))) ∧
    (CurveTest (-(b:ℚ)/(2*a)) (-(k:ℚ)/(2*a)) → Survivor (-(b:ℚ)/(2*a)) (-(k:ℚ)/(2*a)))
instance (a:ℕ) (b:ℤ) (k:ℕ) : Decidable (CheckCandidate a b k) := by
  unfold CheckCandidate; infer_instance

@[expose] def CheckLeading (a:ℕ) : Prop :=
  ∀(b:Fin 325)(k:Fin 162),CheckCandidate a (((b:ℕ):ℤ)-162) ((k:ℕ)+1)
instance (a:ℕ) : Decidable (CheckLeading a) := by unfold CheckLeading; infer_instance

end FiniteSquareTest318
