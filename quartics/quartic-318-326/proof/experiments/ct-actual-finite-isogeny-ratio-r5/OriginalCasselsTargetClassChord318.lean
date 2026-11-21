module
public import OriginalCasselsDyadicXClass318
public import ActualTwoDescentAdjustedChordSquares318
public import Mathlib.Algebra.Polynomial.Derivative
import all ActualTwoDescentAdjustedChordSquares318
public section

noncomputable section

namespace OriginalCasselsTargetClassChord318

open Polynomial OriginalSelectedCasselsParity318 OriginalCasselsDyadicXClass318
open ActualTwoDescentAdjustedChordSquares318
open ActualTwoDescentSquareClassQuotient318

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

private def D (n : F) := 16*n^2

private theorem D_ne {n : F} (hn : n ≠ 0) : D n ≠ 0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero _ hn)

private def coord {n : F} (P : TargetPoint n) : F :=
  match P with
  | .zero => 1
  | .some x _ _ => adjusted (D n) x

private theorem coord_ne {n : F} (hn : n ≠ 0) (P : TargetPoint n) : coord P ≠ 0 := by
  cases P with
  | zero => exact one_ne_zero
  | some x y h => exact adjusted_nonzero _ _ (D_ne hn)

private theorem target_class_of_coord {n : F} (hn : n ≠ 0) (P : TargetPoint n) :
    targetClass P=classOf (coord P) (coord_ne hn P) := by
  cases P with
  | zero => exact class_of_one.symm
  | some x y h =>
    by_cases hx : x=0
    · have he : classOf (D n) (D_ne hn)=1 := by
        rw [←class_of_one]
        apply (class_of_eq_iff _ 1 (D_ne hn) one_ne_zero).mpr
        exact ⟨4*n,mul_ne_zero (by norm_num) hn,by dsimp [D]; ring⟩
      simpa only [targetClass,coord,adjusted,dif_pos hx,if_pos hx] using he.symm
    · simp only [targetClass,coord,adjusted,dif_neg hx,if_neg hx]

private def targetCubic (n : F) : F[X] := X*(X^2-C (4*n)*X+C (16*n^2))
private def line (x y m : F) : F[X] := C m*(X-C x)+C y

private theorem target_chord (n x₁ y₁ x₂ y₂ : F)
    (h₁ : (targetModel n).toAffine.Equation x₁ y₁)
    (h₂ : (targetModel n).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁=x₂ ∧ y₁=(targetModel n).toAffine.negY x₂ y₂)) :
    let m := (targetModel n).toAffine.slope x₁ x₂ y₁ y₂
    let x₃ := (targetModel n).toAffine.addX x₁ x₂ m
    targetCubic n-(line x₁ y₁ m)^2=(X-C x₁)*(X-C x₂)*(X-C x₃) := by
  dsimp only
  let m := (targetModel n).toAffine.slope x₁ x₂ y₁ y₂
  change targetCubic n-(line x₁ y₁ m)^2=
    (X-C x₁)*(X-C x₂)*(X-C ((targetModel n).toAffine.addX x₁ x₂ m))
  have hmodel : (targetModel n).toAffine.addPolynomial x₁ y₁ m =
      -(targetCubic n-(line x₁ y₁ m)^2) := by
    rw [WeierstrassCurve.Affine.addPolynomial_eq]
    simp only [Cubic.toPoly,targetModel,targetCubic,line,map_add,map_sub,map_mul,map_pow,
      map_neg,map_ofNat,map_zero,map_one]
    ring
  have h := WeierstrassCurve.Affine.addPolynomial_slope h₁ h₂ hxy
  change (targetModel n).toAffine.addPolynomial x₁ y₁ m=
    -((X-C x₁)*(X-C x₂)*(X-C ((targetModel n).toAffine.addX x₁ x₂ m))) at h
  exact neg_inj.mp (hmodel.symm.trans h)

private theorem value_and_derivative (n x y m x₁ x₂ x₃ : F)
    (h : targetCubic n-(line x y m)^2=(X-C x₁)*(X-C x₂)*(X-C x₃)) :
    x₁*x₂*x₃=(m*(0-x)+y)^2 ∧
      D n-2*m*(m*(0-x)+y)=x₁*x₂+x₁*x₃+x₂*x₃ := by
  constructor
  · have he := congrArg (Polynomial.eval (0:F)) h
    simp only [targetCubic,line,eval_sub,eval_mul,eval_X,eval_C,eval_add,eval_pow] at he
    linear_combination he
  · have he := congrArg (fun f : F[X] => Polynomial.eval 0 (Polynomial.derivative f)) h
    simp only [targetCubic,line,derivative_sub,derivative_mul,derivative_sq,
      derivative_X,derivative_C,derivative_add,eval_sub,eval_mul,eval_X,eval_C,
      eval_add,eval_pow,eval_natCast,eval_one,eval_zero] at he
    dsimp [D]
    linear_combination he

/-- Chord law on the actual group for the literal quotient cubic.
The derivative normalization at x=0 is retained before squareclass reduction. -/
private theorem adjusted_product_square {n : F} (hn : n ≠ 0) (P Q : TargetPoint n) :
    ∃ s : F, s ≠ 0 ∧ coord P*coord Q*coord (P+Q)=s^2 := by
  cases P with
  | zero =>
    refine ⟨coord Q,coord_ne hn Q,?_⟩
    change (1:F)*coord Q*coord ((0:TargetPoint n)+Q)=(coord Q)^2
    rw [zero_add,one_mul,pow_two]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      let P : TargetPoint n := .some x₁ y₁ h₁
      refine ⟨coord P,coord_ne hn P,?_⟩
      change coord P*(1:F)*coord (P+(0:TargetPoint n))=(coord P)^2
      rw [add_zero,mul_one,pow_two]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁=x₂ ∧ y₁=(targetModel n).toAffine.negY x₂ y₂
      · obtain ⟨hx,hy⟩ := hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
        refine ⟨coord (.some x₁ y₁ h₁),coord_ne hn _,?_⟩
        simp only [coord,mul_one]
        rw [hx]
        ring
      · have h := target_chord n x₁ y₁ x₂ y₂ h₁.left h₂.left hxy
        dsimp only at h
        obtain ⟨hv,hd⟩ := value_and_derivative n x₁ y₁ _ x₁ x₂ _ h
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        exact actual_adjusted_chord_square (D n) x₁ x₂ _ _ _ (D_ne hn) hv hd

private theorem class_square_one (x : F) (hx : x ≠ 0) :
    classOf x hx * classOf x hx=1 := by
  rw [←class_of_mul x x hx hx]
  simpa only [pow_two] using class_of_square x hx

theorem actual_target_class_product (n : F) (hn : n ≠ 0) : XClassProduct n := by
  intro P Q
  obtain ⟨s,hs,he⟩ := adjusted_product_square hn P Q
  have hprod : targetClass P*targetClass Q*targetClass (P+Q)=1 := by
    rw [target_class_of_coord hn P,target_class_of_coord hn Q,target_class_of_coord hn (P+Q),
      ←class_of_mul _ _ (coord_ne hn P) (coord_ne hn Q),
      ←class_of_mul _ _ (mul_ne_zero (coord_ne hn P) (coord_ne hn Q)) (coord_ne hn (P+Q))]
    have he₁ := (class_of_eq_iff _ 1
      (mul_ne_zero (mul_ne_zero (coord_ne hn P) (coord_ne hn Q))
        (coord_ne hn (P+Q))) one_ne_zero).mpr
      ⟨s,hs,by simpa only [one_mul] using he⟩
    exact he₁.trans class_of_one
  have hsq : targetClass (P+Q)*targetClass (P+Q)=1 := by
    rw [target_class_of_coord hn (P+Q)]
    exact class_square_one _ _
  let U : SquareClass F := targetClass P
  let V : SquareClass F := targetClass Q
  let W : SquareClass F := targetClass (P+Q)
  change W=U*V
  have h₁ : U*V*W=1 := hprod
  have h₂ : W*W=1 := hsq
  calc
    W = (1:SquareClass F)*W := (one_mul W).symm
    _ = (U*V*W)*W := congrArg (fun z : SquareClass F => z*W) h₁.symm
    _ = (U*V)*(W*W) := mul_assoc (U*V) W W
    _ = (U*V)*(1:SquareClass F) := congrArg (fun z : SquareClass F => (U*V)*z) h₂
    _ = U*V := mul_one (U*V)

end OriginalCasselsTargetClassChord318

#print axioms OriginalCasselsTargetClassChord318.actual_target_class_product
