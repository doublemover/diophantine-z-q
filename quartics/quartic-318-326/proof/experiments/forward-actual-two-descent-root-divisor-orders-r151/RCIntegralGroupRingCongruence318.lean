module
public import RCSignCharacterCongruence318
public section
noncomputable section
namespace RCIntegralGroupRingCongruence318
open RCSignCharacterCongruence318

def difference {b : ℕ} (G : List (Cube b)) (c : Cube b → ℤ) (x : Cube b) : ℤ :=
  (G.map fun g => c g * (sign g x - 1)).sum

theorem difference_eq {b : ℕ} (G : List (Cube b)) (c : Cube b → ℤ) (x : Cube b) :
    difference G c x = (G.map fun g => c g * sign g x).sum - (G.map c).sum := by
  induction G with
  | nil => simp [difference]
  | cons g G ih =>
      simp only [difference, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem difference_nat_eq {b : ℕ} (G : List (Cube b)) (a : Cube b → ℕ) (x : Cube b) :
    difference G (fun g => (a g : ℤ)) x =
      (G.map fun g => (a g : ℤ) * sign g x).sum - ((G.map a).sum : ℕ) := by
  rw [difference_eq]
  congr 1
  induction G with
  | nil => simp
  | cons g G ih => simp [ih]

/-- Coefficientwise integral congruence transports the literal difference
between evaluation at x and augmentation. -/
theorem difference_congr {b : ℕ} (G : List (Cube b)) (N : ℤ)
    (a c : Cube b → ℤ) (h : ∀ g ∈ G, N ∣ a g - c g) (x : Cube b) :
    N ∣ difference G a x - difference G c x := by
  induction G with
  | nil => simp [difference]
  | cons g G ih =>
      have hh : N ∣ a g - c g := h g (by simp)
      have ht : ∀ g ∈ G, N ∣ a g - c g := by
        intro g hg
        exact h g (by simp [hg])
      have hd := dvd_add (dvd_mul_right_of_dvd hh (sign g x - 1)) (ih ht)
      convert hd using 1 <;> simp only [difference, List.map_cons, List.sum_cons] <;> ring

/-- Finite integral group-ring binary congruences, with arbitrary signed
coefficients. The natural weights are constructed by reduction modulo the
requested power of two; no positivity restriction remains on coefficients. -/
theorem exists_nonzero_integral_congruence (b r M : ℕ)
    (G : List (Cube b)) (c : Fin r → Cube b → ℤ)
    (hsize : r * (2 ^ M - 1) < b) :
    ∃ x : Cube b, x ≠ 0 ∧ ∀ i,
      (2 ^ M : ℤ) ∣ (G.map fun g => c i g * sign g x).sum - (G.map (c i)).sum := by
  let N : ℤ := 2 ^ M
  let a : Fin r → Cube b → ℕ := fun i g => (c i g % N).toNat
  have hN : 0 < N := by dsimp [N]; positivity
  have ha (i : Fin r) (g : Cube b) : (a i g : ℤ) = c i g % N := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hN))
  have hc (i : Fin r) (g : Cube b) : N ∣ (a i g : ℤ) - c i g := by
    refine ⟨-(c i g / N), ?_⟩
    rw [ha]
    have h := Int.emod_add_ediv (c i g) N
    nlinarith
  obtain ⟨x,hx,hw⟩ := exists_nonzero_weighted_congruence b r M G a hsize
  refine ⟨x,hx,fun i => ?_⟩
  have had : N ∣ difference G (fun g => (a i g : ℤ)) x := by
    rw [difference_nat_eq]
    exact hw i
  have hdiff := difference_congr G N (fun g => (a i g : ℤ)) (c i)
    (fun g _ => hc i g) x
  have hcd : N ∣ difference G (c i) x := by
    have h := dvd_sub had hdiff
    simpa only [sub_sub_cancel] using h
  simpa only [N, difference_eq] using hcd

end RCIntegralGroupRingCongruence318
