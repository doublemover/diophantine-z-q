module
public import SparseQuartic
public section

/-! A checked divided-difference test for reflection of a list of quadratic
residuals. The checker works on integer coefficients with a formal parameter
exponent. No coordinate, parameter, polynomial evaluation, or witness is
sampled; computation only tests whether a short linear form is zero. -/

namespace SparseReflectionDifference

variable {n : ℕ}

@[expose] def direction (u v i : Fin n) : ℤ :=
  if i = u then -1 else if i = v then 1 else 0

@[expose] def reflect (u v : Fin n) (w : Fin n → ℚ) (i : Fin n) : ℚ :=
  w i + (direction u v i : ℚ) * (2*w u+1)

theorem reflect_first (u v : Fin n) (w : Fin n → ℚ) :
    reflect u v w u = -1-w u := by
  rw [reflect, direction, if_pos rfl]
  ring

theorem reflect_square (u v : Fin n) (hv : v ≠ u) (w : Fin n → ℚ) :
    reflect u v w v = w v+2*w u+1 := by
  rw [reflect, direction, if_neg hv, if_pos rfl]
  push_cast
  ring

theorem reflect_other {u v i : Fin n} (hu : i ≠ u) (hv : i ≠ v)
    (w : Fin n → ℚ) : reflect u v w i = w i := by
  rw [reflect, direction, if_neg hu, if_neg hv]
  simp

-- The key is (power of S, optional variable); none denotes a constant.
abbrev Key (n : ℕ) := ℕ × Option (Fin n)
abbrev Atom (n : ℕ) := Key n × ℤ

@[expose] def insert (k : Key n) (c : ℤ) : List (Atom n) → List (Atom n)
  | [] => [(k,c)]
  | (j,d)::xs => if k = j then (j,c+d)::xs else (j,d)::insert k c xs

@[expose] def normalize : List (Atom n) → List (Atom n)
  | [] => []
  | (k,c)::xs => if c = 0 then normalize xs else insert k c (normalize xs)

@[expose] def allZero : List (Atom n) → Bool
  | [] => true
  | (_,c)::xs => decide (c=0) && allZero xs

private def value (f : Key n → ℚ) : List (Atom n) → ℚ
  | [] => 0
  | (k,c)::xs => (c:ℚ)*f k+value f xs

private theorem value_append (f : Key n → ℚ) (x y : List (Atom n)) :
    value f (x++y) = value f x + value f y := by
  induction x with
  | nil => exact (zero_add _).symm
  | cons a xs ih =>
    rcases a with ⟨k,c⟩
    change (c:ℚ)*f k+value f (xs++y) = ((c:ℚ)*f k+value f xs)+value f y
    rw [ih, add_assoc]

private theorem value_insert (f : Key n → ℚ) (k : Key n) (c : ℤ) (xs : List (Atom n)) :
    value f (insert k c xs) = (c:ℚ)*f k+value f xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨j,d⟩
    by_cases h : k = j
    · subst j
      rw [insert, if_pos rfl]
      change ((c+d:ℤ):ℚ)*f k+value f xs = (c:ℚ)*f k+((d:ℚ)*f k+value f xs)
      rw [Int.cast_add]
      ring
    · rw [insert, if_neg h]
      change (d:ℚ)*f j+value f (insert k c xs) = (c:ℚ)*f k+((d:ℚ)*f j+value f xs)
      rw [ih]
      ring

private theorem value_normalize (f : Key n → ℚ) (xs : List (Atom n)) :
    value f (normalize xs) = value f xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨k,c⟩
    by_cases h : c = 0
    · subst c
      rw [normalize, if_pos rfl, ih]
      change value f xs = ((0:ℤ):ℚ)*f k+value f xs
      simp
    · rw [normalize, if_neg h, value_insert, ih]

private theorem value_zero (f : Key n → ℚ) (xs : List (Atom n)) (h : allZero xs = true) :
    value f xs = 0 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨k,c⟩
    obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp h
    have hc' : c = 0 := of_decide_eq_true hc
    change (c:ℚ)*f k+value f xs = 0
    rw [hc', ih ht]
    simp

-- Dividing the difference for X_i X_j by L=2X_u+1 gives
-- d_i X_j + d_j X_i + d_i d_j (2X_u+1). No division is used in the proof.
@[expose] def termAtoms (u v : Fin n) (t : SparseQuartic.Term n) : List (Atom n) :=
  let c := t.coefficient
  let e := t.parameterPower
  let d := direction u v
  match t.monomial with
  | .one => []
  | .linear i => [((e,none), c*d i)]
  | .quadratic i j =>
    [((e,some j),c*d i), ((e,some i),c*d j),
     ((e,some u),2*c*d i*d j), ((e,none),c*d i*d j)]

@[expose] def atoms (u v : Fin n) : List (SparseQuartic.Term n) → List (Atom n)
  | [] => []
  | t::ts => termAtoms u v t ++ atoms u v ts

@[expose] def rowOK (u v : Fin n) (ts : List (SparseQuartic.Term n)) : Bool :=
  allZero (normalize (atoms u v ts))

@[expose] def rowsOK (u v : Fin n) : List (List (SparseQuartic.Term n)) → Bool
  | [] => true
  | ts::xs => rowOK u v ts && rowsOK u v xs

private def basis (S : ℤ) (w : Fin n → ℚ) (k : Key n) : ℚ :=
  ((S^k.1:ℤ):ℚ) * k.2.elim 1 w

private theorem term_delta (u v : Fin n) (S : ℤ) (w : Fin n → ℚ) (t : SparseQuartic.Term n) :
    SparseQuartic.termValue S (reflect u v w) t - SparseQuartic.termValue S w t =
      (2*w u+1) * value (basis S w) (termAtoms u v t) := by
  rcases t with ⟨c,e,m⟩
  cases m with
  | one =>
    change ((c*S^e:ℤ):ℚ)*1 - ((c*S^e:ℤ):ℚ)*1 = (2*w u+1)*0
    ring
  | linear i =>
    let d := direction u v
    let L := 2*w u+1
    change ((c*S^e:ℤ):ℚ)*(w i+(d i:ℚ)*L) - ((c*S^e:ℤ):ℚ)*w i =
      L*(((c*d i:ℤ):ℚ)*(((S^e:ℤ):ℚ)*1)+0)
    push_cast
    ring
  | quadratic i j =>
    let d := direction u v
    let L := 2*w u+1
    change ((c*S^e:ℤ):ℚ)*((w i+(d i:ℚ)*L)*(w j+(d j:ℚ)*L)) -
      ((c*S^e:ℤ):ℚ)*(w i*w j) = L*(
        ((c*d i:ℤ):ℚ)*(((S^e:ℤ):ℚ)*w j) +
        (((c*d j:ℤ):ℚ)*(((S^e:ℤ):ℚ)*w i) +
        (((2*c*d i*d j:ℤ):ℚ)*(((S^e:ℤ):ℚ)*w u) +
        (((c*d i*d j:ℤ):ℚ)*(((S^e:ℤ):ℚ)*1)+0))))
    dsimp only [L]
    push_cast
    ring

private theorem residual_cons (S : ℤ) (w : Fin n → ℚ) (t : SparseQuartic.Term n)
    (ts : List (SparseQuartic.Term n)) :
    SparseQuartic.residualValue S w (t::ts) =
      SparseQuartic.termValue S w t+SparseQuartic.residualValue S w ts := by
  simp only [SparseQuartic.residualValue, List.map_cons, List.sum_cons]

private theorem row_delta (u v : Fin n) (S : ℤ) (w : Fin n → ℚ) (ts : List (SparseQuartic.Term n)) :
    SparseQuartic.residualValue S (reflect u v w) ts - SparseQuartic.residualValue S w ts =
      (2*w u+1) * value (basis S w) (atoms u v ts) := by
  induction ts with
  | nil =>
    change (0:ℚ)-0 = (2*w u+1)*0
    ring
  | cons t ts ih =>
    rw [residual_cons, residual_cons, atoms, value_append, mul_add]
    linear_combination term_delta u v S w t + ih

theorem row_preserved (u v : Fin n) (S : ℤ) (w : Fin n → ℚ)
    (ts : List (SparseQuartic.Term n)) (h : rowOK u v ts = true) :
    SparseQuartic.residualValue S (reflect u v w) ts = SparseQuartic.residualValue S w ts := by
  have hz := value_zero (basis S w) (normalize (atoms u v ts)) h
  rw [value_normalize] at hz
  have hd := row_delta u v S w ts
  rw [hz, mul_zero] at hd
  exact sub_eq_zero.mp hd

private theorem squares_preserved (u v : Fin n) (S : ℤ) (w : Fin n → ℚ)
    (rows : List (List (SparseQuartic.Term n))) (h : rowsOK u v rows = true) :
    (rows.map (fun ts => (SparseQuartic.residualValue S (reflect u v w) ts)^2)).sum =
      (rows.map (fun ts => (SparseQuartic.residualValue S w ts)^2)).sum := by
  induction rows with
  | nil => rfl
  | cons ts xs ih =>
    obtain ⟨ha, ht⟩ := Bool.and_eq_true_iff.mp h
    simp only [List.map_cons, List.sum_cons]
    rw [row_preserved u v S w ts ha, ih ht]

theorem polynomial_preserved (u v : Fin n) (S : ℤ) (w : Fin n → ℚ)
    (rows : List (List (SparseQuartic.Term n))) (h : rowsOK u v rows = true) :
    MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (reflect u v w) (SparseQuartic.polynomial S rows) =
      MvPolynomial.eval₂Hom (Int.castRingHom ℚ) w (SparseQuartic.polynomial S rows) := by
  simp only [SparseQuartic.polynomial, map_list_sum, List.map_map, Function.comp_def,
    map_pow, SparseQuartic.eval_residual]
  exact squares_preserved u v S w rows h

end SparseReflectionDifference
