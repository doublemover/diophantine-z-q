module
public import LiteralIntegerDuality318
public section
noncomputable section
namespace OriginalDualIncidenceCount318
open scoped BigOperators
open TernaryQuadraticLineCover318 LiteralDualLineIncidence318 LiteralIntegerDuality318
open LiteralTernaryReduction318
set_option maxHeartbeats 2000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual original lattice parameters annihilated by the integer dual
vector modulo the original squarefree modulus. -/
@[expose] def Incidence (p : ι → ℕ) (κ : ℤ) (v : Vector ℤ) :=
  {t : ∀ i, Option (ZMod (p i)) //
    ∀ u : Vector ℤ, u∈literalLattice p κ t → (FixedSquarefreeCRT318.modulus p:ℤ)∣dot v u}

/-- Exact CRT decomposition of INTEGER-lattice dual incidences. -/
@[expose] def incidenceEquiv (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (v : Vector ℤ) :
    Incidence p κ v ≃
      (∀ i, Direction (κ:ZMod (p i)) (TernaryCongruenceLattices318.reduce (p i) v)) where
  toFun t i := ⟨t.1 i,(original_duality_iff p hp hd κ t.1 v).mp t.2 i⟩
  invFun f := ⟨fun i => (f i).1,(original_duality_iff p hp hd κ (fun i => (f i).1) v).mpr
    (fun i => (f i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Precisely the zero-reduction exception factor. It is not replaced by1
under an unproved primitive-vector assumption. -/
@[expose] def zeroModulus (p : ι → ℕ) (v : Vector ℤ) : ℕ := by
  classical
  exact ∏ i, if TernaryCongruenceLattices318.reduce (p i) v=0 then p i else 1

/-- Uniform exact incidence bound for each original integer vector. Each
nonzero local reduction costs at most2; each zero reduction costs at most2p. -/
theorem original_incidence_bound (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ) (v : Vector ℤ) :
    Nat.card (Incidence p κ v)≤2^(Fintype.card ι)*zeroModulus p v := by
  classical
  letI : ∀ i, Fact (p i).Prime := fun i => ⟨hp i⟩
  have hlocal (i : ι) :
      Nat.card (Direction (κ:ZMod (p i)) (TernaryCongruenceLattices318.reduce (p i) v))≤
        2*(if TernaryCongruenceLattices318.reduce (p i) v=0 then p i else 1) := by
    by_cases hz : TernaryCongruenceLattices318.reduce (p i) v=0
    · rw [hz,direction_card_zero,if_pos rfl,ZMod.card]
      have hh := (hp i).two_le
      omega
    · rw [if_neg hz,mul_one]
      have hk : (κ:ZMod (p i))≠0 := by
        intro he
        exact hκ i ((ZMod.intCast_zmod_eq_zero_iff_dvd κ (p i)).mp he)
      exact direction_card_nonzero (κ:ZMod (p i)) hk _ hz
  rw [Nat.card_congr (incidenceEquiv p hp hd κ v)]
  calc
    _ = ∏ i, Nat.card (Direction (κ:ZMod (p i)) (TernaryCongruenceLattices318.reduce (p i) v)) := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_pi]
    _ ≤ ∏ i, 2*(if TernaryCongruenceLattices318.reduce (p i) v=0 then p i else 1) :=
      Finset.prod_le_prod' (fun i hi => hlocal i)
    _ = 2^(Fintype.card ι)*zeroModulus p v := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const,Finset.card_univ,zeroModulus]

/-- The exception is exactly simultaneous divisibility of the ORIGINAL
three integer coordinates, not divisibility after a rational rescaling. -/
theorem zero_reduction_iff (p : ℕ) (v : Vector ℤ) :
    TernaryCongruenceLattices318.reduce p v=0 ↔
      (p:ℤ)∣v.1 ∧ (p:ℤ)∣v.2.1 ∧ (p:ℤ)∣v.2.2 := by
  change ((v.1:ZMod p),(v.2.1:ZMod p),(v.2.2:ZMod p))=(0,0,0) ↔ _
  simp only [Prod.mk.injEq,ZMod.intCast_zmod_eq_zero_iff_dvd]

end OriginalDualIncidenceCount318
