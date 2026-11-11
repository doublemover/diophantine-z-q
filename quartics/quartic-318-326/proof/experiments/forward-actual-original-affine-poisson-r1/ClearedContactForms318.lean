module
public import ContactPrimeForms318
public section
noncomputable section
namespace ClearedContactForms318
open ContactPrimeForms318
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- A common positive denominator is constructed for every member of the
finite family, not assumed separately at the prime-pattern application. -/
lemma clear_finite {I : Type*} [Fintype I] (a : I → ℚ) :
    ∃ D : ℕ, 0<D ∧ ∃ c : I → ℤ, ∀ i, (c i:ℚ)=a i*(D:ℚ)^2 := by
  classical
  let D := ∏ i, (a i).den
  have hD : 0<D := Finset.prod_pos fun i _ => (a i).den_pos
  have hdiv (i : I) : (a i).den∣D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hint (i : I) : ∃ z : ℤ, (z:ℚ)=a i*(D:ℚ)^2 := by
    obtain ⟨k,hk⟩ := hdiv i
    refine ⟨(a i).num*(k:ℤ)*(D:ℤ),?_⟩
    have he : (D:ℚ)=((a i).den:ℚ)*(k:ℚ) := by exact_mod_cast hk
    have hd : ((a i).den:ℚ)≠0 := by exact_mod_cast (a i).den_ne_zero
    calc
      (((a i).num*(k:ℤ)*(D:ℤ):ℤ):ℚ)=(a i).num*(k:ℚ)*(D:ℚ) := by push_cast <;> rfl
      _ = ((a i).num/((a i).den:ℚ))*(D:ℚ)^2 := by
        rw [he]
        field_simp [hd]
        <;> ring
      _ = a i*(D:ℚ)^2 := by rw [Rat.num_div_den]
  choose c hc using hint
  exact ⟨D,hD,c,hc⟩

structure Clearing (labels : Fin 4 → ℤ) where
  denominator : ℕ
  positive : 0<denominator
  coefficient : Fin 3 × Fin 5 → ℤ
  exact_coefficient : ∀ i, (coefficient i:ℚ)=slope labels i*(denominator:ℚ)^2

@[expose] def construct (labels : Fin 4 → ℤ) : Clearing labels :=
  let h := clear_finite (slope labels)
  { denominator := h.choose
    positive := h.choose_spec.1
    coefficient := h.choose_spec.2.choose
    exact_coefficient := h.choose_spec.2.choose_spec }

variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- Duplicated forms across the three rows are merged only for prime
selection. The original fifteen positions remain attached by coefficient. -/
@[expose] def coefficients : Finset ℤ := Finset.univ.image C.coefficient

lemma coefficient_mem (i : Fin 3 × Fin 5) : C.coefficient i∈coefficients C :=
  Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩

lemma coefficient_eq_iff (i j : Fin 3 × Fin 5) :
    C.coefficient i=C.coefficient j ↔ slope labels i=slope labels j := by
  have hD : (C.denominator:ℚ)^2≠0 := pow_ne_zero 2 (by exact_mod_cast Nat.ne_of_gt C.positive)
  constructor
  · intro h
    have he := congrArg (fun z : ℤ => (z:ℚ)) h
    rw [C.exact_coefficient,C.exact_coefficient] at he
    exact (mul_right_inj' hD).mp he
  · intro h
    apply Int.cast_injective (R:=ℚ)
    rw [C.exact_coefficient,C.exact_coefficient,h]

lemma row_injective (hn : ∀ j, labels j≠0) (j : Fin 3) :
    Function.Injective (fun k => C.coefficient (j,k)) := by
  intro k l h
  exact slope_injective labels hn j ((coefficient_eq_iff C (j,k) (j,l)).mp h)

@[expose] def value (u w k : ℤ) : ℤ := u+k*w^2
@[expose] def parameter (u w : ℤ) : ℚ := (u:ℚ)/((C.denominator:ℚ)*(w:ℚ))^2
@[expose] def rowProduct (u w : ℤ) (j : Fin 3) : ℤ :=
  ∏ k : Fin 5, value u w (C.coefficient (j,k))

lemma value_exact (u w : ℤ) (i : Fin 3 × Fin 5) :
    (value u w (C.coefficient i):ℚ)=
      (u:ℚ)+slope labels i*((C.denominator:ℚ)*(w:ℚ))^2 := by
  simp only [value,Int.cast_add,Int.cast_mul,Int.cast_pow,C.exact_coefficient]
  ring

lemma difference (u w : ℤ) (i j : Fin 3 × Fin 5) :
    value u w (C.coefficient i)-value u w (C.coefficient j)=
      (C.coefficient i-C.coefficient j)*w^2 := by
  unfold value
  ring

end ClearedContactForms318
