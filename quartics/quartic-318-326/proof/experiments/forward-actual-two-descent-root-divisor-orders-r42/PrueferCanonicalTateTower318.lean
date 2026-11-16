module
public import PrimaryTateTower318
public import ActualTwoDescentDyadicPrueferModel318
public section
noncomputable section
namespace PrueferCanonicalTateTower318
open ActualTwoDescentDyadicPrueferModel318

/-- The coordinate at level zero is zero in Q/Z; at level n it is 1/2^n. -/
def circle (n : ℕ) : AddCircle (1 : ℚ) := ((1 : ℚ) / (2 : ℚ)^n : ℚ)

 theorem circle_annihilated (n : ℕ) : (2^n) • circle n = 0 := by
  unfold circle
  rw [← AddCircle.coe_nsmul]
  have h : (2^n : ℕ) • ((1 : ℚ) / (2 : ℚ)^n) = 1 := by
    simp [nsmul_eq_mul]
  rw [h]
  exact AddCircle.coe_period (1 : ℚ)

 theorem circle_transition (n : ℕ) : 2 • circle (n+1) = circle n := by
  unfold circle
  rw [← AddCircle.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_ofNat, pow_succ]
  field_simp
  <;> ring

/-- Each coordinate belongs to the literal primary component, with its
annihilating exponent supplied, rather than to an abstract cyclic model. -/
def point (n : ℕ) : Additive PrueferTwo :=
  Additive.ofMul ⟨Multiplicative.ofAdd (circle n), n, by
    change (2^n) • circle n = 0
    exact circle_annihilated n⟩

 theorem point_annihilated (n : ℕ) : (2^n) • point n = 0 := by
  apply Subtype.ext
  change (2^n) • circle n = 0
  exact circle_annihilated n

 theorem point_transition (n : ℕ) : 2 • point (n+1) = point n := by
  apply Subtype.ext
  change 2 • circle (n+1) = circle n
  exact circle_transition n

/-- A concrete compatible nontrivial tower in the actual Prüfer group. -/
def canonicalTower : PrimaryTateTower318.tower (Additive PrueferTwo) :=
  ⟨point, point_annihilated, point_transition⟩

 theorem circle_one_ne_zero : circle 1 ≠ 0 := by
  intro h
  letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
  have ho : addOrderOf (circle 1) = 2 := by
    simpa [circle] using
      (AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (by norm_num : 0 < (2 : ℕ)))
  rw [h] at ho
  norm_num at ho

 theorem canonicalTower_ne_zero : canonicalTower ≠ 0 := by
  intro h
  have hp : point 1 = 0 := congrArg (fun x => x.val 1) h
  have hc := congrArg (fun x : Additive PrueferTwo => x.toMul.val.toAdd) hp
  exact circle_one_ne_zero hc

end PrueferCanonicalTateTower318
