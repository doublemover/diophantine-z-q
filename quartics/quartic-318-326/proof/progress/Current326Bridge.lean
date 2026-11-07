module
public import Current326Polynomial
public import Current318FinalBridge
import all Current318FinalPolynomial
import all Current326Polynomial
public import ConstantLift326
import all ConstantLift326
public section
namespace Current326Bridge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2048
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def restrict (w : Fin 326 → ℚ) : Fin 318 → ℚ :=
  fun j => w ⟨j.val, by omega⟩

def auxiliary (w : Fin 326 → ℚ) : ConstantLift326.Auxiliary ℚ :=
  ⟨w 318, w 319, w 320, w 321, w 322, w 323, w 324, w 325⟩

def extend (w : Fin 318 → ℚ) (c : ConstantLift326.Auxiliary ℚ) : Fin 326 → ℚ :=
  fun j => if h : j.val < 318 then w ⟨j.val,h⟩ else
    match j.val with
    | 318 => c.c10
    | 319 => c.c11
    | 320 => c.c12
    | 321 => c.c13
    | 322 => c.c14
    | 323 => c.c15
    | 324 => c.c16
    | _ => c.product

theorem restrict_extend (w : Fin 318 → ℚ) (c : ConstantLift326.Auxiliary ℚ) :
    restrict (extend w c) = w := by
  funext j
  simp [restrict, extend, j.isLt]

theorem auxiliary_extend (w : Fin 318 → ℚ) (c : ConstantLift326.Auxiliary ℚ) :
    auxiliary (extend w c) = c := by
  cases c
  rfl

theorem constraints_congr {n m : ℕ} (S T : ℤ) (w : Fin n → ℚ) (v : Fin m → ℚ)
    (rs : List (List (SparseQuartic.Term n))) (ss : List (List (SparseQuartic.Term m)))
    (h : List.Forall₂ (fun r s => SparseQuartic.residualValue S w r = 0 ↔
      SparseQuartic.residualValue T v s = 0) rs ss) :
    SparseQuartic.Constraints S rs w ↔ SparseQuartic.Constraints T ss v := by
  induction h with
  | nil => simp [SparseQuartic.Constraints]
  | @cons r s rs ss hr h ih =>
    simpa only [SparseQuartic.Constraints, List.mem_cons, forall_eq_or_imp] using and_congr hr ih

theorem row0_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row0 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row0 := by
  rfl

theorem row1_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row1 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row1 := by
  rfl

theorem row2_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row2 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row2 := by
  rfl

theorem row3_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row3 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row3 := by
  rfl

theorem row4_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row4 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row4 := by
  rfl

theorem row5_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row5 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row5 := by
  rfl

theorem row6_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row6 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row6 := by
  rfl

theorem row7_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row7 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row7 := by
  rfl

theorem row8_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row8 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row8 := by
  rfl

theorem row9_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row9 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row9 := by
  rfl

theorem row10_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row10 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row10 := by
  rfl

theorem row11_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row11 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row11 := by
  rfl

theorem row12_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row12 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row12 := by
  rfl

theorem row13_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row13 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row13 := by
  rfl

theorem row14_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row14 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row14 := by
  rfl

theorem row15_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row15 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row15 := by
  rfl

theorem row16_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row16 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row16 := by
  rfl

theorem row17_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row17 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row17 := by
  rfl

theorem row18_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row18 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row18 := by
  rfl

theorem row19_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row19 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row19 := by
  rfl

theorem row20_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row20 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row20 := by
  rfl

theorem row21_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row21 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row21 := by
  rfl

theorem row22_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row22 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row22 := by
  rfl

theorem row23_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row23 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row23 := by
  rfl

theorem row24_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row24 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row24 := by
  rfl

theorem row25_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row25 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row25 := by
  rfl

theorem row26_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row26 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row26 := by
  rfl

theorem row27_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row27 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row27 := by
  rfl

theorem row28_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row28 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row28 := by
  rfl

theorem row29_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row29 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row29 := by
  rfl

theorem row30_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row30 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row30 := by
  rfl

theorem row31_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row31 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row31 := by
  rfl

theorem row32_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row32 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row32 := by
  rfl

theorem row33_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row33 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row33 := by
  rfl

theorem row34_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row34 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row34 := by
  rfl

theorem row35_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row35 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row35 := by
  rfl

theorem row36_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row36 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row36 := by
  rfl

theorem row37_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row37 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row37 := by
  rfl

theorem row38_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row38 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row38 := by
  rfl

theorem row39_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row39 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row39 := by
  rfl

theorem row40_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row40 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row40 := by
  rfl

theorem row41_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row41 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row41 := by
  rfl

theorem row42_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row42 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row42 := by
  rfl

theorem row43_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row43 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row43 := by
  rfl

theorem row44_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row44 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row44 := by
  rfl

theorem row45_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row45 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row45 := by
  rfl

theorem row46_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row46 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row46 := by
  rfl

theorem row47_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row47 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row47 := by
  rfl

theorem row48_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row48 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row48 := by
  rfl

theorem row49_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row49 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row49 := by
  rfl

theorem row50_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row50 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row50 := by
  rfl

theorem row51_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row51 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row51 := by
  rfl

theorem row52_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row52 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row52 := by
  rfl

theorem row53_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row53 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row53 := by
  rfl

theorem row54_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row54 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row54 := by
  rfl

theorem row55_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row55 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row55 := by
  rfl

theorem row56_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row56 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row56 := by
  rfl

theorem row57_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row57 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row57 := by
  rfl

theorem row58_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row58 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row58 := by
  rfl

theorem row59_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row59 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row59 := by
  rfl

theorem row60_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row60 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row60 := by
  rfl

theorem row61_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row61 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row61 := by
  rfl

theorem row62_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row62 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row62 := by
  rfl

theorem row63_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row63 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row63 := by
  rfl

theorem row64_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row64 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row64 := by
  rfl

theorem row65_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row65 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row65 := by
  rfl

theorem row66_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row66 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row66 := by
  rfl

theorem row67_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row67 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row67 := by
  rfl

theorem row68_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row68 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row68 := by
  rfl

theorem row69_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row69 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row69 := by
  rfl

theorem row70_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row70 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row70 := by
  rfl

theorem row71_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row71 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row71 := by
  rfl

theorem row72_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row72 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row72 := by
  rfl

theorem row73_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row73 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row73 := by
  rfl

theorem row74_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row74 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row74 := by
  rfl

theorem row75_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row75 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row75 := by
  rfl

theorem row76_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row76 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row76 := by
  rfl

theorem row77_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row77 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row77 := by
  rfl

theorem row78_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row78 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row78 := by
  rfl

theorem row79_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row79 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row79 := by
  rfl

theorem row80_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row80 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row80 := by
  rfl

theorem row81_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row81 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row81 := by
  rfl

theorem row82_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row82 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row82 := by
  rfl

theorem row83_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row83 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row83 := by
  rfl

theorem row84_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row84 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row84 := by
  rfl

theorem row85_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row85 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row85 := by
  rfl

theorem row86_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row86 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row86 := by
  rfl

theorem row87_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row87 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row87 := by
  rfl

theorem row88_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row88 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row88 := by
  rfl

theorem row89_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row89 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row89 := by
  rfl

theorem row90_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row90 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row90 := by
  rfl

theorem row91_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row91 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row91 := by
  rfl

theorem row92_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row92 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row92 := by
  rfl

theorem row93_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row93 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row93 := by
  rfl

theorem row94_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row94 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row94 := by
  rfl

theorem row95_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row95 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row95 := by
  rfl

theorem row96_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row96 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row96 := by
  rfl

theorem row97_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row97 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row97 := by
  rfl

theorem row98_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row98 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row98 := by
  rfl

theorem row99_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row99 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row99 := by
  rfl

theorem row100_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row100 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row100 := by
  rfl

theorem row101_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row101 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row101 := by
  rfl

theorem row102_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row102 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row102 := by
  rfl

theorem row103_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row103 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row103 := by
  rfl

theorem row104_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row104 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row104 := by
  rfl

theorem row105_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row105 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row105 := by
  rfl

theorem row106_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row106 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row106 := by
  rfl

theorem row107_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row107 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row107 := by
  rfl

theorem row108_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row108 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row108 := by
  rfl

theorem row109_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row109 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row109 := by
  rfl

theorem row110_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row110 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row110 := by
  rfl

theorem row111_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row111 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row111 := by
  rfl

theorem row112_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row112 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row112 := by
  rfl

theorem row113_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row113 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row113 := by
  rfl

theorem row114_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row114 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row114 := by
  rfl

theorem row115_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row115 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row115 := by
  rfl

theorem row116_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row116 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row116 := by
  rfl

theorem row117_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row117 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row117 := by
  rfl

theorem row118_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row118 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row118 := by
  rfl

theorem row119_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row119 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row119 := by
  rfl

theorem row120_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row120 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row120 := by
  rfl

theorem row121_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row121 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row121 := by
  rfl

theorem row122_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row122 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row122 := by
  rfl

theorem row123_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row123 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row123 := by
  rfl

theorem row124_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row124 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row124 := by
  rfl

theorem row125_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row125 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row125 := by
  rfl

theorem row126_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row126 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row126 := by
  rfl

theorem row127_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row127 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row127 := by
  rfl

theorem row128_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row128 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row128 := by
  rfl

theorem row129_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row129 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row129 := by
  rfl

theorem row130_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row130 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row130 := by
  rfl

theorem row131_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row131 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row131 := by
  rfl

theorem row132_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row132 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row132 := by
  rfl

theorem row133_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row133 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row133 := by
  rfl

theorem row134_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row134 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row134 := by
  rfl

theorem row135_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row135 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row135 := by
  rfl

theorem row136_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row136 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row136 := by
  rfl

theorem row137_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row137 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row137 := by
  rfl

theorem row138_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row138 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row138 := by
  rfl

theorem row139_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row139 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row139 := by
  rfl

theorem row140_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row140 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row140 := by
  rfl

theorem row141_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row141 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row141 := by
  rfl

theorem row142_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row142 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row142 := by
  rfl

theorem row143_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row143 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row143 := by
  rfl

theorem row144_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row144 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row144 := by
  rfl

theorem row145_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row145 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row145 := by
  rfl

theorem row146_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row146 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row146 := by
  rfl

theorem row147_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row147 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row147 := by
  rfl

theorem row148_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row148 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row148 := by
  rfl

theorem row149_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row149 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row149 := by
  rfl

theorem row150_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row150 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row150 := by
  rfl

theorem row151_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row151 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row151 := by
  rfl

theorem row152_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row152 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row152 := by
  rfl

theorem row153_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row153 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row153 := by
  rfl

theorem row154_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row154 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row154 := by
  rfl

theorem row155_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row155 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row155 := by
  rfl

theorem row156_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row156 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row156 := by
  rfl

theorem row157_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row157 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row157 := by
  rfl

theorem row158_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row158 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row158 := by
  rfl

theorem row159_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row159 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row159 := by
  rfl

theorem row160_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row160 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row160 := by
  rfl

theorem row161_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row161 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row161 := by
  rfl

theorem row162_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row162 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row162 := by
  rfl

theorem row163_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row163 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row163 := by
  rfl

theorem row164_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row164 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row164 := by
  rfl

theorem row165_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row165 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row165 := by
  rfl

theorem row166_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row166 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row166 := by
  rfl

theorem row167_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row167 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row167 := by
  rfl

theorem row168_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row168 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row168 := by
  rfl

theorem row169_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row169 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row169 := by
  rfl

theorem row170_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row170 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row170 := by
  rfl

theorem row171_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row171 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row171 := by
  rfl

theorem row172_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row172 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row172 := by
  rfl

theorem row173_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row173 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row173 := by
  rfl

theorem row174_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row174 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row174 := by
  rfl

theorem row175_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row175 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row175 := by
  rfl

theorem row176_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row176 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row176 := by
  rfl

theorem row177_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row177 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row177 := by
  rfl

theorem row178_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row178 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row178 := by
  rfl

theorem row179_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row179 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row179 := by
  rfl

theorem row180_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row180 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row180 := by
  rfl

theorem row181_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row181 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row181 := by
  rfl

theorem row182_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row182 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row182 := by
  rfl

theorem row183_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row183 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row183 := by
  rfl

theorem row184_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row184 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row184 := by
  rfl

theorem row185_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row185 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row185 := by
  rfl

theorem row186_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row186 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row186 := by
  rfl

theorem row187_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row187 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row187 := by
  rfl

theorem row188_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row188 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row188 := by
  rfl

theorem row189_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row189 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row189 := by
  rfl

theorem row190_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row190 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row190 := by
  rfl

theorem row191_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row191 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row191 := by
  rfl

theorem row192_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row192 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row192 := by
  rfl

theorem row193_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row193 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row193 := by
  rfl

theorem row194_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row194 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row194 := by
  rfl

theorem row195_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row195 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row195 := by
  rfl

theorem row196_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row196 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row196 := by
  rfl

theorem row197_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row197 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row197 := by
  rfl

theorem row198_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row198 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row198 := by
  rfl

theorem row199_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row199 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row199 := by
  rfl

theorem row200_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row200 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row200 := by
  rfl

theorem row201_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row201 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row201 := by
  rfl

theorem row202_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row202 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row202 := by
  rfl

theorem row203_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row203 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row203 := by
  rfl

theorem row204_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row204 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row204 := by
  rfl

theorem row205_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row205 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row205 := by
  rfl

theorem row206_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row206 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row206 := by
  rfl

theorem row207_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row207 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row207 := by
  rfl

theorem row208_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row208 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row208 := by
  rfl

theorem row209_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row209 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row209 := by
  rfl

theorem row210_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row210 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row210 := by
  rfl

theorem row211_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row211 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row211 := by
  rfl

theorem row212_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row212 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row212 := by
  rfl

theorem row213_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row213 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row213 := by
  rfl

theorem row214_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row214 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row214 := by
  rfl

theorem row215_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row215 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row215 := by
  rfl

theorem row216_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row216 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row216 := by
  rfl

theorem row217_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row217 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row217 := by
  rfl

theorem row218_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row218 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row218 := by
  rfl

theorem row219_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row219 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row219 := by
  rfl

theorem row220_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row220 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row220 := by
  rfl

theorem row221_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row221 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row221 := by
  rfl

theorem row222_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row222 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row222 := by
  rfl

theorem row223_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row223 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row223 := by
  rfl

theorem row224_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row224 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row224 := by
  rfl

theorem row225_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row225 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row225 := by
  rfl

theorem row226_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row226 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row226 := by
  rfl

theorem row227_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row227 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row227 := by
  rfl

theorem row228_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row228 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row228 := by
  rfl

theorem row229_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row229 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row229 := by
  rfl

theorem row230_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row230 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row230 := by
  rfl

theorem row231_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row231 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row231 := by
  rfl

theorem row232_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row232 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row232 := by
  rfl

theorem row233_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row233 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row233 := by
  rfl

theorem row234_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row234 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row234 := by
  rfl

theorem row235_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row235 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row235 := by
  rfl

theorem row236_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row236 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row236 := by
  rfl

theorem row237_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row237 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row237 := by
  rfl

theorem row238_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row238 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row238 := by
  rfl

theorem row239_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row239 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row239 := by
  rfl

theorem row240_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row240 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row240 := by
  rfl

theorem row241_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row241 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row241 := by
  rfl

theorem row242_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row242 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row242 := by
  rfl

theorem row243_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row243 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row243 := by
  rfl

theorem row244_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row244 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row244 := by
  rfl

theorem row245_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row245 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row245 := by
  rfl

theorem row246_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row246 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row246 := by
  rfl

theorem row247_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row247 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row247 := by
  rfl

theorem row248_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row248 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row248 := by
  rfl

theorem row249_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row249 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row249 := by
  rfl

theorem row250_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row250 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row250 := by
  rfl

theorem row251_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row251 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row251 := by
  rfl

theorem row252_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row252 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row252 := by
  rfl

theorem row253_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row253 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row253 := by
  rfl

theorem row254_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row254 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row254 := by
  rfl

theorem row255_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row255 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row255 := by
  rfl

theorem row256_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row256 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row256 := by
  rfl

theorem row257_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row257 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row257 := by
  rfl

theorem row258_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row258 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row258 := by
  rfl

theorem row259_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row259 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row259 := by
  rfl

theorem row260_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row260 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row260 := by
  rfl

theorem row261_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row261 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row261 := by
  rfl

theorem row262_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row262 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row262 := by
  rfl

theorem row263_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row263 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row263 := by
  rfl

theorem row264_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row264 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row264 := by
  rfl

theorem row265_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row265 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row265 := by
  rfl

theorem row266_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row266 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row266 := by
  rfl

theorem row267_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row267 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row267 := by
  rfl

theorem row268_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row268 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row268 := by
  rfl

theorem row269_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row269 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row269 := by
  rfl

theorem row270_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row270 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row270 := by
  rfl

theorem row271_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row271 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row271 := by
  rfl

theorem row272_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row272 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row272 := by
  rfl

theorem row273_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row273 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row273 := by
  rfl

theorem row274_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row274 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row274 := by
  rfl

theorem row275_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row275 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row275 := by
  simp only [Current326Polynomial.row275, Current318FinalPolynomial.row275,
    SparseQuartic.residualValue, SparseQuartic.termValue, SparseQuartic.monomialValue,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [restrict]
  simp only [hP, hS]; ring

theorem row276_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row276 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row276 := by
  rfl

theorem row277_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row277 =
      -SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row277 := by
  simp only [Current326Polynomial.row277, Current318FinalPolynomial.row277,
    SparseQuartic.residualValue, SparseQuartic.termValue, SparseQuartic.monomialValue,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [restrict]
  simp only [hP, hS]; ring

theorem row278_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row278 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row278 := by
  rfl

theorem row279_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row279 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row279 := by
  rfl

theorem row280_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row280 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row280 := by
  rfl

theorem row281_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row281 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row281 := by
  rfl

theorem row282_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row282 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row282 := by
  rfl

theorem row283_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row283 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row283 := by
  rfl

theorem row284_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row284 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row284 := by
  rfl

theorem row285_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row285 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row285 := by
  rfl

theorem row286_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row286 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row286 := by
  rfl

theorem row287_identity (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.residualValue S w Current326Polynomial.row287 =
      SparseQuartic.residualValue S (restrict w) Current318FinalPolynomial.row287 := by
  simp only [Current326Polynomial.row287, Current318FinalPolynomial.row287,
    SparseQuartic.residualValue, SparseQuartic.termValue, SparseQuartic.monomialValue,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [restrict]
  simp only [hP, hS]; ring

def oldRows : List (List (SparseQuartic.Term 326)) := [Current326Polynomial.row0, Current326Polynomial.row1, Current326Polynomial.row2, Current326Polynomial.row3, Current326Polynomial.row4, Current326Polynomial.row5, Current326Polynomial.row6, Current326Polynomial.row7, Current326Polynomial.row8, Current326Polynomial.row9, Current326Polynomial.row10, Current326Polynomial.row11, Current326Polynomial.row12, Current326Polynomial.row13, Current326Polynomial.row14, Current326Polynomial.row15, Current326Polynomial.row16, Current326Polynomial.row17, Current326Polynomial.row18, Current326Polynomial.row19, Current326Polynomial.row20, Current326Polynomial.row21, Current326Polynomial.row22, Current326Polynomial.row23, Current326Polynomial.row24, Current326Polynomial.row25, Current326Polynomial.row26, Current326Polynomial.row27, Current326Polynomial.row28, Current326Polynomial.row29, Current326Polynomial.row30, Current326Polynomial.row31, Current326Polynomial.row32, Current326Polynomial.row33, Current326Polynomial.row34, Current326Polynomial.row35, Current326Polynomial.row36, Current326Polynomial.row37, Current326Polynomial.row38, Current326Polynomial.row39, Current326Polynomial.row40, Current326Polynomial.row41, Current326Polynomial.row42, Current326Polynomial.row43, Current326Polynomial.row44, Current326Polynomial.row45, Current326Polynomial.row46, Current326Polynomial.row47, Current326Polynomial.row48, Current326Polynomial.row49, Current326Polynomial.row50, Current326Polynomial.row51, Current326Polynomial.row52, Current326Polynomial.row53, Current326Polynomial.row54, Current326Polynomial.row55, Current326Polynomial.row56, Current326Polynomial.row57, Current326Polynomial.row58, Current326Polynomial.row59, Current326Polynomial.row60, Current326Polynomial.row61, Current326Polynomial.row62, Current326Polynomial.row63, Current326Polynomial.row64, Current326Polynomial.row65, Current326Polynomial.row66, Current326Polynomial.row67, Current326Polynomial.row68, Current326Polynomial.row69, Current326Polynomial.row70, Current326Polynomial.row71, Current326Polynomial.row72, Current326Polynomial.row73, Current326Polynomial.row74, Current326Polynomial.row75, Current326Polynomial.row76, Current326Polynomial.row77, Current326Polynomial.row78, Current326Polynomial.row79, Current326Polynomial.row80, Current326Polynomial.row81, Current326Polynomial.row82, Current326Polynomial.row83, Current326Polynomial.row84, Current326Polynomial.row85, Current326Polynomial.row86, Current326Polynomial.row87, Current326Polynomial.row88, Current326Polynomial.row89, Current326Polynomial.row90, Current326Polynomial.row91, Current326Polynomial.row92, Current326Polynomial.row93, Current326Polynomial.row94, Current326Polynomial.row95, Current326Polynomial.row96, Current326Polynomial.row97, Current326Polynomial.row98, Current326Polynomial.row99, Current326Polynomial.row100, Current326Polynomial.row101, Current326Polynomial.row102, Current326Polynomial.row103, Current326Polynomial.row104, Current326Polynomial.row105, Current326Polynomial.row106, Current326Polynomial.row107, Current326Polynomial.row108, Current326Polynomial.row109, Current326Polynomial.row110, Current326Polynomial.row111, Current326Polynomial.row112, Current326Polynomial.row113, Current326Polynomial.row114, Current326Polynomial.row115, Current326Polynomial.row116, Current326Polynomial.row117, Current326Polynomial.row118, Current326Polynomial.row119, Current326Polynomial.row120, Current326Polynomial.row121, Current326Polynomial.row122, Current326Polynomial.row123, Current326Polynomial.row124, Current326Polynomial.row125, Current326Polynomial.row126, Current326Polynomial.row127, Current326Polynomial.row128, Current326Polynomial.row129, Current326Polynomial.row130, Current326Polynomial.row131, Current326Polynomial.row132, Current326Polynomial.row133, Current326Polynomial.row134, Current326Polynomial.row135, Current326Polynomial.row136, Current326Polynomial.row137, Current326Polynomial.row138, Current326Polynomial.row139, Current326Polynomial.row140, Current326Polynomial.row141, Current326Polynomial.row142, Current326Polynomial.row143, Current326Polynomial.row144, Current326Polynomial.row145, Current326Polynomial.row146, Current326Polynomial.row147, Current326Polynomial.row148, Current326Polynomial.row149, Current326Polynomial.row150, Current326Polynomial.row151, Current326Polynomial.row152, Current326Polynomial.row153, Current326Polynomial.row154, Current326Polynomial.row155, Current326Polynomial.row156, Current326Polynomial.row157, Current326Polynomial.row158, Current326Polynomial.row159, Current326Polynomial.row160, Current326Polynomial.row161, Current326Polynomial.row162, Current326Polynomial.row163, Current326Polynomial.row164, Current326Polynomial.row165, Current326Polynomial.row166, Current326Polynomial.row167, Current326Polynomial.row168, Current326Polynomial.row169, Current326Polynomial.row170, Current326Polynomial.row171, Current326Polynomial.row172, Current326Polynomial.row173, Current326Polynomial.row174, Current326Polynomial.row175, Current326Polynomial.row176, Current326Polynomial.row177, Current326Polynomial.row178, Current326Polynomial.row179, Current326Polynomial.row180, Current326Polynomial.row181, Current326Polynomial.row182, Current326Polynomial.row183, Current326Polynomial.row184, Current326Polynomial.row185, Current326Polynomial.row186, Current326Polynomial.row187, Current326Polynomial.row188, Current326Polynomial.row189, Current326Polynomial.row190, Current326Polynomial.row191, Current326Polynomial.row192, Current326Polynomial.row193, Current326Polynomial.row194, Current326Polynomial.row195, Current326Polynomial.row196, Current326Polynomial.row197, Current326Polynomial.row198, Current326Polynomial.row199, Current326Polynomial.row200, Current326Polynomial.row201, Current326Polynomial.row202, Current326Polynomial.row203, Current326Polynomial.row204, Current326Polynomial.row205, Current326Polynomial.row206, Current326Polynomial.row207, Current326Polynomial.row208, Current326Polynomial.row209, Current326Polynomial.row210, Current326Polynomial.row211, Current326Polynomial.row212, Current326Polynomial.row213, Current326Polynomial.row214, Current326Polynomial.row215, Current326Polynomial.row216, Current326Polynomial.row217, Current326Polynomial.row218, Current326Polynomial.row219, Current326Polynomial.row220, Current326Polynomial.row221, Current326Polynomial.row222, Current326Polynomial.row223, Current326Polynomial.row224, Current326Polynomial.row225, Current326Polynomial.row226, Current326Polynomial.row227, Current326Polynomial.row228, Current326Polynomial.row229, Current326Polynomial.row230, Current326Polynomial.row231, Current326Polynomial.row232, Current326Polynomial.row233, Current326Polynomial.row234, Current326Polynomial.row235, Current326Polynomial.row236, Current326Polynomial.row237, Current326Polynomial.row238, Current326Polynomial.row239, Current326Polynomial.row240, Current326Polynomial.row241, Current326Polynomial.row242, Current326Polynomial.row243, Current326Polynomial.row244, Current326Polynomial.row245, Current326Polynomial.row246, Current326Polynomial.row247, Current326Polynomial.row248, Current326Polynomial.row249, Current326Polynomial.row250, Current326Polynomial.row251, Current326Polynomial.row252, Current326Polynomial.row253, Current326Polynomial.row254, Current326Polynomial.row255, Current326Polynomial.row256, Current326Polynomial.row257, Current326Polynomial.row258, Current326Polynomial.row259, Current326Polynomial.row260, Current326Polynomial.row261, Current326Polynomial.row262, Current326Polynomial.row263, Current326Polynomial.row264, Current326Polynomial.row265, Current326Polynomial.row266, Current326Polynomial.row267, Current326Polynomial.row268, Current326Polynomial.row269, Current326Polynomial.row270, Current326Polynomial.row271, Current326Polynomial.row272, Current326Polynomial.row273, Current326Polynomial.row274, Current326Polynomial.row275, Current326Polynomial.row276, Current326Polynomial.row277, Current326Polynomial.row278, Current326Polynomial.row279, Current326Polynomial.row280, Current326Polynomial.row281, Current326Polynomial.row282, Current326Polynomial.row283, Current326Polynomial.row284, Current326Polynomial.row285, Current326Polynomial.row286, Current326Polynomial.row287]
def auxRows : List (List (SparseQuartic.Term 326)) := [Current326Polynomial.row288, Current326Polynomial.row289, Current326Polynomial.row290, Current326Polynomial.row291, Current326Polynomial.row292, Current326Polynomial.row293, Current326Polynomial.row294, Current326Polynomial.row295]
theorem old_constraints_iff (S : ℤ) (w : Fin 326 → ℚ)
    (hS : w 324 = (S : ℚ)) (hP : w 325 = (S : ℚ) * w 145) :
    SparseQuartic.Constraints S oldRows w ↔
      SparseQuartic.Constraints S Current318FinalPolynomial.rows (restrict w) := by
  apply constraints_congr
  exact 
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row0_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row1_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row2_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row3_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row4_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row5_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row6_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row7_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row8_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row9_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row10_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row11_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row12_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row13_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row14_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row15_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row16_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row17_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row18_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row19_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row20_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row21_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row22_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row23_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row24_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row25_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row26_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row27_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row28_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row29_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row30_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row31_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row32_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row33_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row34_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row35_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row36_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row37_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row38_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row39_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row40_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row41_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row42_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row43_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row44_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row45_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row46_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row47_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row48_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row49_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row50_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row51_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row52_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row53_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row54_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row55_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row56_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row57_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row58_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row59_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row60_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row61_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row62_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row63_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row64_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row65_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row66_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row67_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row68_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row69_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row70_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row71_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row72_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row73_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row74_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row75_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row76_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row77_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row78_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row79_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row80_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row81_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row82_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row83_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row84_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row85_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row86_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row87_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row88_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row89_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row90_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row91_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row92_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row93_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row94_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row95_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row96_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row97_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row98_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row99_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row100_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row101_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row102_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row103_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row104_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row105_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row106_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row107_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row108_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row109_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row110_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row111_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row112_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row113_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row114_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row115_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row116_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row117_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row118_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row119_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row120_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row121_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row122_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row123_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row124_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row125_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row126_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row127_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row128_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row129_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row130_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row131_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row132_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row133_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row134_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row135_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row136_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row137_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row138_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row139_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row140_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row141_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row142_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row143_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row144_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row145_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row146_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row147_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row148_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row149_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row150_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row151_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row152_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row153_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row154_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row155_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row156_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row157_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row158_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row159_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row160_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row161_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row162_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row163_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row164_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row165_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row166_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row167_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row168_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row169_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row170_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row171_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row172_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row173_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row174_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row175_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row176_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row177_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row178_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row179_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row180_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row181_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row182_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row183_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row184_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row185_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row186_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row187_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row188_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row189_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row190_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row191_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row192_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row193_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row194_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row195_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row196_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row197_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row198_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row199_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row200_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row201_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row202_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row203_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row204_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row205_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row206_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row207_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row208_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row209_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row210_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row211_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row212_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row213_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row214_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row215_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row216_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row217_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row218_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row219_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row220_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row221_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row222_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row223_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row224_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row225_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row226_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row227_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row228_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row229_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row230_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row231_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row232_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row233_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row234_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row235_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row236_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row237_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row238_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row239_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row240_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row241_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row242_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row243_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row244_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row245_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row246_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row247_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row248_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row249_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row250_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row251_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row252_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row253_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row254_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row255_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row256_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row257_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row258_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row259_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row260_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row261_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row262_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row263_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row264_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row265_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row266_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row267_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row268_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row269_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row270_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row271_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row272_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row273_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row274_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row275_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row276_identity S w hS hP)).to_iff) (
List.Forall₂.cons (by rw [row277_identity S w hS hP, neg_eq_zero]) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row278_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row279_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row280_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row281_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row282_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row283_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row284_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row285_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row286_identity S w hS hP)).to_iff) (
List.Forall₂.cons ((congrArg (fun x : ℚ => x = 0) (row287_identity S w hS hP)).to_iff) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem aux_constraints_iff (S : ℤ) (w : Fin 326 → ℚ) :
    SparseQuartic.Constraints S auxRows w ↔
      ConstantLift326.Constraints ((3 : ℚ)^1024) (w 145) (auxiliary w) := by
  simp only [auxRows, SparseQuartic.Constraints, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp]
  norm_num [Current326Polynomial.row288, Current326Polynomial.row289,
    Current326Polynomial.row290, Current326Polynomial.row291,
    Current326Polynomial.row292, Current326Polynomial.row293,
    Current326Polynomial.row294, Current326Polynomial.row295,
    SparseQuartic.residualValue, SparseQuartic.termValue, SparseQuartic.monomialValue,
    ConstantLift326.Constraints, auxiliary, pow_two]
  constructor <;> rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith, by linarith, by nlinarith⟩

theorem constraints_split (S : ℤ) (w : Fin 326 → ℚ) :
    SparseQuartic.Constraints S Current326Polynomial.rows w ↔
      SparseQuartic.Constraints S oldRows w ∧ SparseQuartic.Constraints S auxRows w := by
  change SparseQuartic.Constraints S (oldRows ++ auxRows) w ↔ _
  simp only [SparseQuartic.Constraints, List.mem_append, or_imp, forall_and]

theorem scale_cast : (Current318FinalPolynomial.scale : ℚ) = (3 : ℚ)^(2^16) := by
  simp only [Current318FinalPolynomial.scale, Int.cast_pow, Int.cast_ofNat]

theorem constraints_iff (w : Fin 326 → ℚ) :
    SparseQuartic.Constraints Current326Polynomial.scale Current326Polynomial.rows w ↔
      SparseQuartic.Constraints Current318FinalPolynomial.scale
        Current318FinalPolynomial.rows (restrict w) ∧
      ConstantLift326.Constraints ((3 : ℚ)^1024) (w 145) (auxiliary w) := by
  change SparseQuartic.Constraints Current318FinalPolynomial.scale Current326Polynomial.rows w ↔ _
  rw [constraints_split, aux_constraints_iff]
  constructor
  · rintro ⟨hold,haux⟩
    have hout := ConstantLift326.concrete_outputs (w 145) (auxiliary w) haux
    have hS : w 324 = (Current318FinalPolynomial.scale : ℚ) := by
      rw [scale_cast]
      exact hout.1
    have hP : w 325 = (Current318FinalPolynomial.scale : ℚ) * w 145 := by
      rw [scale_cast]
      exact hout.2
    exact ⟨(old_constraints_iff _ w hS hP).mp hold, haux⟩
  · rintro ⟨hold,haux⟩
    have hout := ConstantLift326.concrete_outputs (w 145) (auxiliary w) haux
    have hS : w 324 = (Current318FinalPolynomial.scale : ℚ) := by
      rw [scale_cast]
      exact hout.1
    have hP : w 325 = (Current318FinalPolynomial.scale : ℚ) * w 145 := by
      rw [scale_cast]
      exact hout.2
    exact ⟨(old_constraints_iff _ w hS hP).mpr hold, haux⟩

def canonicalExtend (w : Fin 318 → ℚ) : Fin 326 → ℚ :=
  extend w (ConstantLift326.canonical ((3 : ℚ)^1024) (w 145))

theorem canonicalExtend_restrict (w : Fin 318 → ℚ) :
    restrict (canonicalExtend w) = w := restrict_extend _ _

theorem canonicalExtend_zero (w : Fin 318 → ℚ) : canonicalExtend w 0 = w 0 := by rfl

theorem canonicalExtend_satisfies (w : Fin 318 → ℚ) :
    SparseQuartic.Constraints Current326Polynomial.scale Current326Polynomial.rows
      (canonicalExtend w) ↔
    SparseQuartic.Constraints Current318FinalPolynomial.scale Current318FinalPolynomial.rows w := by
  rw [constraints_iff, canonicalExtend_restrict]
  have haux : ConstantLift326.Constraints ((3 : ℚ)^1024)
      (canonicalExtend w 145) (auxiliary (canonicalExtend w)) := by
    change ConstantLift326.Constraints ((3 : ℚ)^1024) (w 145)
      (auxiliary (extend w (ConstantLift326.canonical ((3 : ℚ)^1024) (w 145))))
    rw [auxiliary_extend]
    exact ConstantLift326.canonical_satisfies _ _
  exact and_iff_left haux

theorem reconstruct (w : Fin 326 → ℚ) : extend (restrict w) (auxiliary w) = w := by
  funext j
  rcases j with ⟨j,hj⟩
  by_cases h : j < 318
  · simp [extend, restrict, h]
  · have hj' : 318 ≤ j := by omega
    interval_cases j <;> rfl

theorem unique_lift (w : Fin 326 → ℚ)
    (h : SparseQuartic.Constraints Current326Polynomial.scale Current326Polynomial.rows w) :
    w = canonicalExtend (restrict w) := by
  have haux := ((constraints_iff w).mp h).2
  have heq := (ConstantLift326.unique_extension _ _ _).mp haux
  rw [← reconstruct w]
  change extend (restrict w) (auxiliary w) =
    extend (restrict (extend (restrict w) (auxiliary w)))
      (ConstantLift326.canonical ((3 : ℚ)^1024)
        (restrict (extend (restrict w) (auxiliary w)) 145))
  rw [restrict_extend]
  exact congrArg (extend (restrict w)) heq

theorem witnesses_iff (q : ℚ) :
    (∃ w : Fin 325 → ℚ, SparseQuartic.Constraints Current326Polynomial.scale
      Current326Polynomial.rows (Fin.cons q w)) ↔
    (∃ w : Fin 317 → ℚ, SparseQuartic.Constraints Current318FinalPolynomial.scale
      Current318FinalPolynomial.rows (Fin.cons q w)) := by
  constructor
  · rintro ⟨w,hw⟩
    have h := ((constraints_iff (Fin.cons q w)).mp hw).1
    refine ⟨Fin.tail (restrict (Fin.cons q w)), ?_⟩
    have heq : Fin.cons q (Fin.tail (restrict (Fin.cons q w))) = restrict (Fin.cons q w) := by
      conv_lhs => lhs; change restrict (Fin.cons q w) 0
      exact Fin.cons_self_tail _
    rw [heq]
    exact h
  · rintro ⟨w,hw⟩
    have h := (canonicalExtend_satisfies (Fin.cons q w)).mpr hw
    refine ⟨Fin.tail (canonicalExtend (Fin.cons q w)), ?_⟩
    have heq : Fin.cons q (Fin.tail (canonicalExtend (Fin.cons q w))) =
        canonicalExtend (Fin.cons q w) := by
      conv_lhs => lhs; change canonicalExtend (Fin.cons q w) 0
      exact Fin.cons_self_tail _
    rw [heq]
    exact h

theorem polynomial_zero_iff_318 (q : ℚ) :
    (∃ w : Fin 325 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current326Polynomial.P = 0) ↔
    (∃ w : Fin 317 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current318FinalPolynomial.P = 0) := by
  exact (Current326Polynomial.input_projection_iff q).trans
    ((witnesses_iff q).trans (Current318FinalPolynomial.input_projection_iff q).symm)

theorem polynomial_zero_iff_source (q : ℚ) :
    (∃ w : Fin 325 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current326Polynomial.P = 0) ↔
    CircuitReplay.HasSolution
      (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale : ℚ)) q :=
  (polynomial_zero_iff_318 q).trans (Current318FinalBridge.polynomial_zero_iff_source q)

/-- This finite lift does not remove the unproved global sourceArithmetic premise. -/
theorem defines_integers_of_source_arithmetic
    (sourceArithmetic : ∀ q : ℚ,
      CircuitReplay.HasSolution (Raw318FinalReplay.stage0 (Current318FinalPolynomial.scale : ℚ)) q ↔
        ∃ z : ℤ, (z : ℚ) = q) :
    ∀ q : ℚ, (∃ w : Fin 325 → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ)
      (Fin.cons q w) Current326Polynomial.P = 0) ↔ ∃ z : ℤ, (z : ℚ) = q := by
  intro q
  exact (polynomial_zero_iff_source q).trans (sourceArithmetic q)

end Current326Bridge
