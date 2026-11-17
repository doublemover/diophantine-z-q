module
public import ActualPreparedPoleSmallSupport318
public section
noncomputable section
namespace ActualPreparedPoleMutualRoots318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPoleSupport318
open ActualPreparedPoleSmallSupport318

/-- The local/denominator portion of the EXISTING preparation at the
same rational pole. No rank, Selmer, symbols, or rational-point premises. -/
structure Preparation (b : ℚ) : Prop where
  positive : 0<b
  small : b<17
  denominator_square : IsSquare b.den
  square_two : IsSquare (b:ℚ_[2])
  depth_two : 3≤padicValRat 2 b
  square_three : IsSquare (b:ℚ_[3])
  depth_three : 1≤padicValRat 3 b
  depth_seventeen : 2≤padicValRat 17 b

/-- Consume the literal conjunction already exported by
ThreeSelectedPolePreparation318.Prepared at each original contact pole. -/
def Preparation.of_conditions {b : ℚ}
    (h : 0<b ∧ b<17 ∧ IsSquare b.den ∧ IsSquare (b:ℚ_[2]) ∧
      3≤padicValRat 2 b ∧ IsSquare (b:ℚ_[3]) ∧ 1≤padicValRat 3 b ∧
      IsSquare (b:ℚ_[17]) ∧ 2≤padicValRat 17 b) : Preparation b := by
  obtain ⟨hb,hs,hd,h2,v2,h3,v3,_,v17⟩ := h
  exact ⟨hb,hs,hd,h2,v2,h3,v3,v17⟩

/-- Both squarefree supports avoid the actual small primes2 and3. -/
theorem avoid_two_three {b : ℚ} (C : Classes b) (H : Preparation b) :
    (¬2∣C.beta) ∧ (¬3∣C.beta) ∧ (¬2∣C.theta) ∧ (¬3∣C.theta) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  have v2 : padicValRat 2 (17:ℚ)=0 := by
    rw [show (17:ℚ)=((17:ℕ):ℚ) from rfl,padicValRat.of_nat,
      padicValNat_primes (by decide : 2≠17)]
    rfl
  have v3 : padicValRat 3 (17:ℚ)=0 := by
    rw [show (17:ℚ)=((17:ℕ):ℚ) from rfl,padicValRat.of_nat,
      padicValNat_primes (by decide : 3≠17)]
    rfl
  refine ⟨beta_not_dvd_of_local_square C (ne_of_gt H.positive) (by decide) H.square_two,
    beta_not_dvd_of_local_square C (ne_of_gt H.positive) (by decide) H.square_three,
    theta_not_dvd_of_depth C H.positive H.small (p:=2) ?_,
    theta_not_dvd_of_depth C H.positive H.small (p:=3) ?_⟩
  · rw [v2]
    have hh := H.depth_two
    omega
  · rw [v3]
    have hh := H.depth_three
    omega

/-- The exact two finite supports have no common prime, with2 now
excluded from actual preparation rather than added as an assumption. -/
theorem disjoint_support {b : ℚ} (C : Classes b) (H : Preparation b)
    {p : ℕ} [Fact p.Prime] (hpb : p∣C.beta) : ¬p∣C.theta := by
  have hp2 : p≠2 := by
    intro he
    subst p
    exact (avoid_two_three C H).1 hpb
  exact no_common_odd_prime C (ne_of_gt H.positive) H.denominator_square
    H.depth_seventeen hp2 hpb

/-- Actual local roots in both directions at EVERY support prime.
Residue classes modulo24 and genuine global point production remain
separate, not silently supplied by this local theorem. -/
theorem mutual_roots {b : ℚ} (C : Classes b) (H : Preparation b) :
    (∀ p, ∀ [Fact p.Prime], p∣C.beta →
      ∃ r : ℚ_[p], r≠0 ∧ r^2=(C.theta:ℚ_[p])) ∧
    (∀ p, ∀ [Fact p.Prime], p∣C.theta →
      ∃ r : ℚ_[p], r≠0 ∧ r^2=(C.beta:ℚ_[p])) := by
  constructor
  · intro p hp hpb
    have hp2 : p≠2 := by
      intro he
      subst p
      exact (avoid_two_three C H).1 hpb
    exact theta_square_at_beta_support C (ne_of_gt H.positive) H.denominator_square
      H.depth_seventeen hp2 hpb
  · intro p hp hpt
    have hp2 : p≠2 := by
      intro he
      subst p
      exact (avoid_two_three C H).2.2.1 hpt
    exact ActualPreparedPoleSmallSupport318.beta_square_at_theta_support C
      H.positive H.small H.denominator_square H.depth_seventeen hp2 hpt

end ActualPreparedPoleMutualRoots318
