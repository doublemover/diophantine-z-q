module
public import OriginalPhysicalHZ210Coefficients318
public section
namespace OriginalPhysicalHZ210Map318
open Polynomial
open OriginalPhysicalHZ210Coefficients318
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

@[expose] def horner {R : Type*} [CommRing R] (z : R) : List ℤ → R
  | [] => 0
  | c :: l => (c : R) + z * horner z l
@[expose] def val {R : Type*} [CommRing R] (a b c : R) (t : Term) : R :=
  (t.coeff : R) * (a^t.i * b^t.j * c^t.k)
@[expose] def form {R : Type*} [CommRing R] (a b c : R) : List Term → R
  | [] => 0
  | t :: l => val a b c t + form a b c l
@[expose] def physical {R : Type*} [CommRing R] (z : R) : R :=
  form (horner z A) (horner z B) (horner z OriginalPhysicalHZ210Coefficients318.C) terms

theorem horner_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : R) (l : List ℤ) :
    f (horner z l) = horner (f z) l := by
  induction l with
  | nil => exact map_zero f
  | cons c l ih => simp only [horner, map_add, map_intCast, map_mul, ih]
theorem form_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b c : R) (l : List Term) :
    f (form a b c l) = form (f a) (f b) (f c) l := by
  induction l with
  | nil => exact map_zero f
  | cons t l ih => simp only [form, val, map_add, map_mul, map_pow, map_intCast, ih]
theorem physical_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : R) :
    f (physical z) = physical (f z) := by simp only [physical, form_map, horner_map]
theorem horner_degree (l : List ℤ) : (horner (X : ℤ[X]) l).natDegree ≤ l.length := by
  induction l with
  | nil => simp [horner]
  | cons c l ih =>
    apply natDegree_add_le_of_degree_le
    · simp
    · exact (natDegree_mul_le_of_le natDegree_X_le ih).trans (by simp [Nat.add_comm])

@[expose] def within (t : Term) : Bool := decide (5*t.i + 13*t.j + 21*t.k ≤ 300)
theorem bounded : terms.all within = true := by decide
theorem physical_degree : (physical (X : ℤ[X])).natDegree ≤ 300 := by
  have h {l : List Term} (hl : l.all within = true) :
      (form (horner (X : ℤ[X]) A) (horner X B) (horner X OriginalPhysicalHZ210Coefficients318.C) l).natDegree ≤ 300 := by
    induction l with
    | nil => simp [form]
    | cons t l ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hl
      apply natDegree_add_le_of_degree_le _ (ih hl.2)
      have h := natDegree_mul_le_of_le
        (natDegree_mul_le_of_le (natDegree_pow_le_of_le t.i (horner_degree A))
          (natDegree_pow_le_of_le t.j (horner_degree B)))
        (natDegree_pow_le_of_le t.k (horner_degree OriginalPhysicalHZ210Coefficients318.C))
      have h' : 5*t.i+13*t.j+21*t.k≤300 := of_decide_eq_true hl.1
      have hlA : A.length=5 := rfl
      have hlB : B.length=13 := rfl
      have hlC : OriginalPhysicalHZ210Coefficients318.C.length=21 := rfl
      rw [hlA, hlB, hlC] at h
      apply (natDegree_mul_le_of_le (show ((t.coeff : ℤ[X])).natDegree ≤ 0 by simp) h).trans
      simpa only [Nat.zero_add, Nat.mul_comm] using h'
  exact h bounded

end OriginalPhysicalHZ210Map318
