module
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public section
namespace BoundedPrimaryTowerVanishing318

/-- Iterating the actual transition equation, with a fixed common tower. -/
lemma iterate_transition {G : Type*} [AddCommGroup G] (x : ℕ → G)
    (hx : ∀ k, 2 • x (k+1)=x k) (k m : ℕ) :
    (2^m) • x (k+m)=x k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ,mul_nsmul']
    have he : 2 • x (k+(m+1))=x (k+m) := by
      simpa only [Nat.add_assoc] using hx (k+m)
    rw [he]
    exact ih

/-- A uniformly bounded two-primary group has no nonzero compatible
infinite halving tower. This is proved algebraically, without compactness
or an assumed finite-Sha conclusion. -/
theorem tower_zero_of_bounded_exponent {G : Type*} [AddCommGroup G]
    (N : ℕ) (hN : ∀ g : G, (2^N) • g=0)
    (x : ℕ → G) (hx : ∀ k, 2 • x (k+1)=x k) : ∀ k, x k=0 := by
  intro k
  calc
    x k = (2^N) • x (k+N) := (iterate_transition x hx k N).symm
    _ = 0 := hN _

/-- The finite cyclic models in the actual Selmer classification therefore
contribute no compatible halving tower, before any Z2-module interpretation. -/
theorem finite_cyclic_tower_zero (N : ℕ) (x : ℕ → ZMod (2^N))
    (hx : ∀ k, 2 • x (k+1)=x k) : ∀ k, x k=0 := by
  apply tower_zero_of_bounded_exponent N _ x hx
  intro g
  simp [nsmul_eq_mul]

end BoundedPrimaryTowerVanishing318
