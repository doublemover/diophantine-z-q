module
public import Current326Polynomial
public import Mathlib.Data.List.Sort
public section
namespace Current326CoefficientBindingNormalize
abbrev Entry := List (Fin 326) × ℤ

@[expose] def collect : List Entry → List Entry
  | [] => []
  | x :: xs => match collect xs with
    | [] => [x]
    | y :: ys => if x.1 = y.1 then (x.1, x.2 + y.2) :: ys else x :: y :: ys

/-- Fuel is used only to make the computation structurally recursive. If fuel
runs out, concatenation still preserves interpretation. -/
@[expose] def merge : ℕ → List Entry → List Entry → List Entry
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
      if compare x.1 y.1 != .gt then x :: merge fuel xs (y :: ys)
      else y :: merge fuel (x :: xs) ys

@[expose] def pairPass : List (List Entry) → List (List Entry)
  | xs :: ys :: rest => merge (xs.length + ys.length) xs ys :: pairPass rest
  | runs => runs

@[expose] def passes : ℕ → List (List Entry) → List (List Entry)
  | 0, runs => runs
  | n + 1, runs => passes n (pairPass runs)

/-- Thirteen passes suffice for the current finite input, but preservation
below holds for arbitrary inputs even if more passes would be needed to sort. -/
@[expose] def sortEntries (xs : List Entry) : List Entry :=
  (passes 13 (xs.map (fun x => [x]))).flatten

@[expose] def normalize (xs : List Entry) : List Entry :=
  (collect (sortEntries xs)).filter (fun e => e.2 != 0)

@[expose] def evaluate {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M) (xs : List Entry) : M :=
  (xs.map (fun e => e.2 • f e.1)).sum

@[simp] theorem evaluate_nil {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M) :
    evaluate f [] = 0 := rfl
@[simp] theorem evaluate_cons {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (x : Entry) (xs : List Entry) : evaluate f (x :: xs) = x.2 • f x.1 + evaluate f xs := rfl

theorem evaluate_append {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (xs ys : List Entry) : evaluate f (xs ++ ys) = evaluate f xs + evaluate f ys := by
  simp only [evaluate, List.map_append, List.sum_append]

theorem evaluate_flatten {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (xs : List (List Entry)) : evaluate f xs.flatten = (xs.map (evaluate f)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatten_cons, evaluate_append, ih, List.map_cons, List.sum_cons]

theorem evaluate_collect {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (xs : List Entry) : evaluate f (collect xs) = evaluate f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [collect]
    cases h : collect xs with
    | nil =>
      simpa only [h, evaluate_nil, evaluate_cons, add_zero] using congrArg (fun y => x.2 • f x.1 + y) ih
    | cons y ys =>
      by_cases he : x.1 = y.1
      · simp only [he, if_pos, evaluate_cons, add_zsmul]
        rw [h, evaluate_cons] at ih
        rw [← ih]
        exact add_assoc _ _ _
      · simp only [if_neg he, evaluate_cons]
        rw [h, evaluate_cons] at ih
        rw [ih]

theorem evaluate_filter {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (xs : List Entry) : evaluate f (xs.filter (fun e => e.2 != 0)) = evaluate f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x.2 = 0
    · simp [h, ih]
    · simp [h, ih]

theorem evaluate_merge {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (fuel : ℕ) (xs ys : List Entry) :
    evaluate f (merge fuel xs ys) = evaluate f xs + evaluate f ys := by
  induction fuel generalizing xs ys with
  | zero => exact evaluate_append f xs ys
  | succ fuel ih =>
    cases xs with
    | nil => simp [merge]
    | cons x xs =>
      cases ys with
      | nil => simp [merge]
      | cons y ys =>
        simp only [merge]
        split <;> simp only [evaluate_cons, ih] <;> abel

theorem evaluate_pairPass {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (runs : List (List Entry)) :
    evaluate f (pairPass runs).flatten = evaluate f runs.flatten := by
  cases runs with
  | nil => rfl
  | cons xs rest =>
    cases rest with
    | nil => rfl
    | cons ys rest =>
      simp only [pairPass, List.flatten_cons, evaluate_append, evaluate_merge]
      rw [evaluate_pairPass f rest]
      abel
termination_by runs.length

theorem evaluate_passes {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (n : ℕ) (runs : List (List Entry)) :
    evaluate f (passes n runs).flatten = evaluate f runs.flatten := by
  induction n generalizing runs with
  | zero => rfl
  | succ n ih =>
    exact (ih (pairPass runs)).trans (evaluate_pairPass f runs)

theorem evaluate_sort {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (xs : List Entry) : evaluate f (sortEntries xs) = evaluate f xs := by
  rw [sortEntries, evaluate_passes]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change x.2 • f x.1 + evaluate f ((xs.map (fun x => [x])).flatten) =
      x.2 • f x.1 + evaluate f xs
    rw [ih]

theorem evaluate_normalize {M : Type*} [AddCommGroup M] (f : List (Fin 326) → M)
    (xs : List Entry) : evaluate f (normalize xs) = evaluate f xs := by
  rw [normalize, evaluate_filter, evaluate_collect, evaluate_sort]

end Current326CoefficientBindingNormalize
