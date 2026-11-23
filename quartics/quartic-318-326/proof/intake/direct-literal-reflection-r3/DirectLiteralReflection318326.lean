module
public import SparseReflectionDifference
public import Current318FinalPolynomial
public import Current326CoefficientBinding
public section

namespace DirectLiteralReflection318326
open SparseReflectionDifference (reflect rowsOK polynomial_preserved)

-- These two approvals are kernel reduction of closed integer coefficient
-- lists. In particular the fixed tower scale is never evaluated by the checker.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
theorem rows318_checked : rowsOK 0 118 Current318FinalPolynomial.rows = true := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3000000 in
theorem rows326_checked : rowsOK 0 118 Current326Polynomial.rows = true := by
  decide +kernel

/-- All 318 coordinates are quantified, and the conclusion is an equality of
values, not only an equality of their vanishing loci. -/
theorem published318 (w : Fin 318 → ℚ) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (reflect 0 118 w) Current318FinalPolynomial.P =
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w Current318FinalPolynomial.P :=
  polynomial_preserved 0 118 Current318FinalPolynomial.scale w _ rows318_checked

/-- Explicit stored coefficient table, not just its sparse SOS presentation. -/
theorem stored326 (w : Fin 326 → ℚ) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (reflect 0 118 w)
        Current326CoefficientBinding.tablePolynomial =
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w Current326CoefficientBinding.tablePolynomial := by
  rw [Current326CoefficientBinding.table_eq_sos]
  exact polynomial_preserved 0 118 Current326Polynomial.scale w _ rows326_checked

/-- The public polynomial evaluated at the input followed by exactly n witnesses. -/
def HasZero {n : ℕ} (p : MvPolynomial (Fin (n+1)) ℤ) (q : ℚ) : Prop :=
  ∃ w : Fin n → ℚ, MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (Fin.cons q w) p = 0

private theorem project {n : ℕ} (p : MvPolynomial (Fin (n+1)) ℤ)
    (v : Fin (n+1))
    (hp : ∀ w, MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (reflect 0 v w) p =
      MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w p) (q : ℚ) :
    HasZero p q → HasZero p (-1-q) := by
  rintro ⟨w,hw⟩
  let z := reflect 0 v (Fin.cons q w)
  have hz : z 0 = -1-q := by
    change reflect 0 v (Fin.cons q w) 0 = -1-q
    rw [SparseReflectionDifference.reflect_first, Fin.cons_zero]
  refine ⟨Fin.tail z, ?_⟩
  rw [← hz, Fin.cons_self_tail]
  exact (hp _).trans hw

private theorem project_iff {n : ℕ} (p : MvPolynomial (Fin (n+1)) ℤ)
    (v : Fin (n+1))
    (hp : ∀ w, MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (reflect 0 v w) p =
      MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w p) (q : ℚ) :
    HasZero p (-1-q) ↔ HasZero p q := by
  refine ⟨?_, project p v hp q⟩
  intro h
  have k := project p v hp (-1-q) h
  rwa [show (-1-(-1-q) : ℚ) = q by ring] at k

theorem original_zero_sets (q : ℚ) :
    (HasZero Current318FinalPolynomial.P (-1-q) ↔ HasZero Current318FinalPolynomial.P q) ∧
    (HasZero Current326CoefficientBinding.tablePolynomial (-1-q) ↔
      HasZero Current326CoefficientBinding.tablePolynomial q) :=
  ⟨project_iff _ 118 published318 q, project_iff _ 118 stored326 q⟩

-- On the actual square-defining row these mutants lose a bona fide zero.
-- Coordinate zero is still reflected correctly; only the auxiliary update changes.
@[expose] def mutant {n : ℕ} (u v : Fin n) (offset slope : ℚ) (w : Fin n → ℚ) (i : Fin n) : ℚ :=
  if i = u then -1-w u else if i = v then w v+slope*w u+offset else w i

private theorem row79_form318 (S : ℤ) (w : Fin 318 → ℚ) :
    SparseQuartic.residualValue S w Current318FinalPolynomial.row79 = (w 0)^2-w 118 := by
  change ((1*S^0:ℤ):ℚ)*(w 0*w 0)+(((-1*S^0:ℤ):ℚ)*w 118+0) = (w 0)^2-w 118
  rw [pow_zero]
  ring

private theorem row79_form326 (S : ℤ) (w : Fin 326 → ℚ) :
    SparseQuartic.residualValue S w Current326Polynomial.row79 = (w 0)^2-w 118 := by
  change ((1*S^0:ℤ):ℚ)*(w 0*w 0)+(((-1*S^0:ℤ):ℚ)*w 118+0) = (w 0)^2-w 118
  rw [pow_zero]
  ring

theorem reject_missing_constant :
    SparseQuartic.residualValue Current318FinalPolynomial.scale
      (mutant 0 118 0 2 (fun _ => 0)) Current318FinalPolynomial.row79 = 1 ∧
    SparseQuartic.residualValue Current326Polynomial.scale
      (mutant 0 118 0 2 (fun _ => 0)) Current326Polynomial.row79 = 1 ∧
    SparseQuartic.residualValue Current318FinalPolynomial.scale
      (fun _ => 0) Current318FinalPolynomial.row79 = 0 ∧
    SparseQuartic.residualValue Current326Polynomial.scale
      (fun _ => 0) Current326Polynomial.row79 = 0 := by
  simp only [row79_form318, row79_form326]
  decide +kernel

theorem reject_negative_slope :
    SparseQuartic.residualValue Current318FinalPolynomial.scale
      (mutant 0 118 1 (-2) (fun _ => 1)) Current318FinalPolynomial.row79 = 4 ∧
    SparseQuartic.residualValue Current326Polynomial.scale
      (mutant 0 118 1 (-2) (fun _ => 1)) Current326Polynomial.row79 = 4 ∧
    SparseQuartic.residualValue Current318FinalPolynomial.scale
      (fun _ => 1) Current318FinalPolynomial.row79 = 0 ∧
    SparseQuartic.residualValue Current326Polynomial.scale
      (fun _ => 1) Current326Polynomial.row79 = 0 := by
  simp only [row79_form318, row79_form326]
  decide +kernel

end DirectLiteralReflection318326

#print axioms DirectLiteralReflection318326.published318
#print axioms DirectLiteralReflection318326.stored326
#print axioms DirectLiteralReflection318326.original_zero_sets
