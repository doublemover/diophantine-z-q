module
public import OriginalRCTerminalCertificate318
public import OriginalRCLaurentFiniteConvolution318
public import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.BigOperators.Finsupp.Basic

open scoped BigOperators

public section

noncomputable section

namespace OriginalRCLiteralTerminalRows318
open OriginalRCTerminalAddress318 OriginalRCTerminalWindow318 OriginalRCTerminalCertificate318
open OriginalRCLaurentFiniteConvolution318

variable {R G : Type*} [CommRing R] [Group G]
variable {b M L : ℕ}

abbrev Series (M : ℕ) := HahnSeries ℤ (Residue M)

/-- The actual finite sign evaluation of an original group algebra
element, using the supplied original character and coefficient map. -/
@[expose] def evaluate (rho : R →+* Series M) (chi : G →* Series M) :
    MonoidAlgebra R G →+* Series M :=
  MonoidAlgebra.liftNCRingHom rho chi (fun a g => mul_comm (rho a) (chi g))

theorem basis_expansion (label : Finset (Fin b) ≃ G) (f : MonoidAlgebra R G) :
    (∑ S : Finset (Fin b), MonoidAlgebra.single (label S) (f.coeff (label S))) = f := by
  classical
  letI : Fintype G := Fintype.ofEquiv (Finset (Fin b)) label
  calc
    _ = ∑ g : G, MonoidAlgebra.single g (f.coeff g) :=
      Equiv.sum_comp label (fun g => MonoidAlgebra.single g (f.coeff g))
    _ = f := by
      have he := Finsupp.sum_fintype f.coeff MonoidAlgebra.single
        (fun g => MonoidAlgebra.single_zero g)
      exact he.symm.trans (MonoidAlgebra.sum_coeff_single f)

theorem signed_coeff (V : Series M) (x : Fin b → ZMod 2) (S : Finset (Fin b)) (i : ℤ) :
    (V * ∏ j ∈ S, (if x j = 0 then (1 : Series M) else -1)).coeff i =
      V.coeff i * ∏ j ∈ S, (if x j = 0 then (1 : Residue M) else -1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj]
      by_cases h : x j = 0
      · simpa only [h, if_true, one_mul] using ih
      · simpa only [h, if_false, neg_one_mul, mul_neg, HahnSeries.coeff_neg] using
          congrArg Neg.neg ih

/-- This is the literal labelled coefficient of f in the original group
basis, after the genuine finite coefficient map. -/
@[expose] def coefficientRow (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
    (f : MonoidAlgebra R G) (i : ℤ) (S : Finset (Fin b)) : Residue M :=
  (rho (f.coeff (label S))).coeff i

theorem coefficient_signRow (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
    (chi : G →* Series M) (f : MonoidAlgebra R G) (i : ℤ) (x : Fin b → ZMod 2)
    (hchi : ∀ S : Finset (Fin b), chi (label S) =
      ∏ j ∈ S, (if x j = 0 then (1 : Series M) else -1)) :
    (evaluate rho chi f).coeff i = signRow M b (coefficientRow label rho f i) x := by
  classical
  calc
    _ = (evaluate rho chi (∑ S : Finset (Fin b),
        MonoidAlgebra.single (label S) (f.coeff (label S)))).coeff i := by
      exact congrArg (fun v : MonoidAlgebra R G => (evaluate rho chi v).coeff i)
        (basis_expansion label f).symm
    _ = _ := by
      simp only [map_sum, HahnSeries.coeff_sum, signRow]
      apply Finset.sum_congr rfl
      intro S _
      rw [evaluate, MonoidAlgebra.liftNCRingHom_single, hchi, signed_coeff] <;> rfl

/-- The old exactly L+2 tests. No negative coefficient of d is
invented, and the f tests have the old -(j+1) orientation. -/
@[expose] def literalTests (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
    (f d : MonoidAlgebra R G) : Tests b M L :=
  fun i =>
    if i.val < L then coefficientRow label rho f (-((i.val : ℤ)+1))
    else if i.val = L then coefficientRow label rho f 0
    else coefficientRow label rho d 0

theorem literal_negative_test (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
    (chi : G →* Series M) (f d : MonoidAlgebra R G) (x : Fin b → ZMod 2)
    (hchi : ∀ S : Finset (Fin b), chi (label S) =
      ∏ j ∈ S, (if x j = 0 then (1 : Series M) else -1)) (j : Fin L) :
    testValue (literalTests label rho f d) (negativeSlot j) x =
      (evaluate rho chi f).coeff (-((j.val : ℤ)+1)) := by
  simpa only [testValue, literalTests, negativeSlot, j.isLt, if_true] using
    (coefficient_signRow label rho chi f _ x hchi).symm

theorem literal_F_test (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
    (chi : G →* Series M) (f d : MonoidAlgebra R G) (x : Fin b → ZMod 2)
    (hchi : ∀ S : Finset (Fin b), chi (label S) =
      ∏ j ∈ S, (if x j = 0 then (1 : Series M) else -1)) :
    testValue (literalTests label rho f d) (constantFSlot L) x = (evaluate rho chi f).coeff 0 := by
  simpa only [testValue, literalTests, constantFSlot, lt_irrefl, if_false, if_true] using
    (coefficient_signRow label rho chi f 0 x hchi).symm

theorem literal_D_test (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
    (chi : G →* Series M) (f d : MonoidAlgebra R G) (x : Fin b → ZMod 2)
    (hchi : ∀ S : Finset (Fin b), chi (label S) =
      ∏ j ∈ S, (if x j = 0 then (1 : Series M) else -1)) :
    testValue (literalTests label rho f d) (constantDSlot L) x = (evaluate rho chi d).coeff 0 := by
  have h₁ : ¬ L+1 < L := Nat.not_lt_of_ge (Nat.le_succ L)
  have h₂ : L+1 ≠ L := Nat.succ_ne_self L
  simpa only [testValue, literalTests, constantDSlot, h₁, h₂, if_false] using
    (coefficient_signRow label rho chi d 0 x hchi).symm

/-- The exact old terminal row is recovered from the actual scaled
regular product and full Laurent cutoff, rather than stipulated on
arbitrary certificate tests. Positive terms are scaled coefficients. -/
theorem scaled_test_row (label : Finset (Fin b) ≃ G) (rho : R →+* Series M)
    (chi : G →* Series M) (f d : MonoidAlgebra R G) (x : Fin b → ZMod 2)
    (hchi : ∀ S : Finset (Fin b), chi (label S) =
      ∏ j ∈ S, (if x j = 0 then (1 : Series M) else -1))
    (U : PowerSeries (Residue M)) (c : ℕ)
    (hF : ∀ n : ℤ, n < -(L : ℤ) → (evaluate rho chi f).coeff n = 0)
    (hProd : HahnSeries.C ((2 : Residue M)^c) * evaluate rho chi d =
      evaluate rho chi f * HahnSeries.ofPowerSeries ℤ (Residue M) U) :
    (2 : Residue M)^c * testValue (literalTests label rho f d) (constantDSlot L) x =
      testValue (literalTests label rho f d) (constantFSlot L) x * PowerSeries.constantCoeff U +
        ∑ j : Fin L, testValue (literalTests label rho f d) (negativeSlot j) x *
          PowerSeries.coeff (j.val+1) U := by
  simpa only [literal_negative_test label rho chi f d x hchi,
    literal_F_test label rho chi f d x hchi, literal_D_test label rho chi f d x hchi] using
    scaled_constant_window L ((2 : Residue M)^c) (evaluate rho chi f) (evaluate rho chi d) U hF hProd

end OriginalRCLiteralTerminalRows318

#print axioms OriginalRCLiteralTerminalRows318.scaled_test_row
