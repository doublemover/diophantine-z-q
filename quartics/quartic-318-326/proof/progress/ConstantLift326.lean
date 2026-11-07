module
public import Mathlib.Tactic
public section

/-! The eight auxiliary coordinates of the 326-variable construction have
exactly one extension for each old assignment. This checks only the constant
chain and product gate, not the literal 296-row polynomial replay. -/
namespace ConstantLift326

variable {R : Type*} [CommSemiring R]

structure Auxiliary (R : Type*) where
  c10 : R
  c11 : R
  c12 : R
  c13 : R
  c14 : R
  c15 : R
  c16 : R
  product : R
  deriving DecidableEq

def Constraints (seed norm : R) (c : Auxiliary R) : Prop :=
  c.c10 = seed ∧ c.c11 = c.c10^2 ∧ c.c12 = c.c11^2 ∧
  c.c13 = c.c12^2 ∧ c.c14 = c.c13^2 ∧ c.c15 = c.c14^2 ∧
  c.c16 = c.c15^2 ∧ c.product = c.c16 * norm

def canonical (seed norm : R) : Auxiliary R :=
  ⟨seed, seed^2, seed^4, seed^8, seed^16, seed^32,
    seed^64, seed^64 * norm⟩

theorem canonical_satisfies (seed norm : R) :
    Constraints seed norm (canonical seed norm) := by
  norm_num [Constraints, canonical, ← pow_mul]

theorem unique_extension (seed norm : R) (c : Auxiliary R) :
    Constraints seed norm c ↔ c = canonical seed norm := by
  constructor
  · rcases c with ⟨c0,c1,c2,c3,c4,c5,c6,p⟩
    intro h
    change c0 = seed ∧ c1 = c0^2 ∧ c2 = c1^2 ∧ c3 = c2^2 ∧
      c4 = c3^2 ∧ c5 = c4^2 ∧ c6 = c5^2 ∧ p = c6 * norm at h
    rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,hp⟩
    subst c0; subst c1; subst c2; subst c3; subst c4; subst c5; subst c6; subst p
    norm_num [canonical, ← pow_mul]
  · rintro rfl
    exact canonical_satisfies seed norm

theorem exists_unique_extension (seed norm : R) :
    ∃! c : Auxiliary R, Constraints seed norm c := by
  refine ⟨canonical seed norm, canonical_satisfies seed norm, ?_⟩
  intro c hc
  exact (unique_extension seed norm c).mp hc

theorem concrete_terminal : ((3 : R)^1024)^64 = (3 : R)^(2^16) := by
  simpa only [show (1024 * 64 : ℕ) = 2^16 by decide] using
    (pow_mul (3 : R) 1024 64).symm

theorem concrete_outputs (norm : R) (c : Auxiliary R)
    (h : Constraints ((3 : R)^1024) norm c) :
    c.c16 = (3 : R)^(2^16) ∧ c.product = (3 : R)^(2^16) * norm := by
  rw [(unique_extension _ _ _).mp h]
  simp only [canonical, concrete_terminal, and_self]

/-- Any predicate on the old variables, terminal constant, and product is
preserved by the unique extension. The concrete residual correspondence must
still be instantiated and checked separately. -/
theorem eliminate_auxiliary (seed norm : R) (F : R → R → Prop) :
    (∃ c : Auxiliary R, Constraints seed norm c ∧ F c.c16 c.product) ↔
      F (seed^64) (seed^64 * norm) := by
  constructor
  · rintro ⟨c,hc,hF⟩
    rw [(unique_extension _ _ _).mp hc] at hF
    exact hF
  · intro hF
    exact ⟨canonical seed norm, canonical_satisfies seed norm, hF⟩

theorem eliminate_concrete_auxiliary (norm : R) (F : R → R → Prop) :
    (∃ c : Auxiliary R, Constraints ((3 : R)^1024) norm c ∧ F c.c16 c.product) ↔
      F ((3 : R)^(2^16)) ((3 : R)^(2^16) * norm) := by
  rw [eliminate_auxiliary, concrete_terminal (R := R)]

end ConstantLift326

#print axioms ConstantLift326.canonical_satisfies
#print axioms ConstantLift326.unique_extension
#print axioms ConstantLift326.exists_unique_extension
#print axioms ConstantLift326.concrete_terminal
#print axioms ConstantLift326.concrete_outputs
#print axioms ConstantLift326.eliminate_auxiliary
#print axioms ConstantLift326.eliminate_concrete_auxiliary
