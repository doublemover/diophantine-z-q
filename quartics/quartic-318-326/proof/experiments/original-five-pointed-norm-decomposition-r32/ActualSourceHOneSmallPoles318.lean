module
public import ActualSourceHOnePrincipalRepresentatives318
public import ContactFinitePoleReduction318

public section
noncomputable section
namespace ActualSourceHOneSmallPoles318
open RootOrderMonomialBasis318 ContactFinitePoleReduction318
open ActualSourceHOnePrincipalRepresentatives318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A rationally weighted pole monomial in the original overlap, followed by
the original boundary. No rational module structure on H1 is presupposed. -/
@[expose] def poleClass (q : ℚ) (k : ℕ) (i : ThreeIndex) : HOne :=
  boundary (algebraMap ℚ (ContactKummerOrder318.OpenOrder units) q *
    ContactInfinityRegularFractions318.inverseU units ^ k *
    InfinityOverlapLocalization318.toOpen units (ContactHOneOrderBases318.infinityBasis units i))

/-- All high-pole classes vanish because the weighted witness is in the
original finite ring, not merely regular in the contact function field. -/
theorem poleClass_zero_of_weight_le (q : ℚ) (k : ℕ) (i : ThreeIndex)
    (hk : weight i ≤ k) : poleClass q k i = 0 := by
  have hw : algebraMap ℚ (ContactKummerOrder318.OpenOrder units) q *
      SourceOpenFractionField318.orderToOpen units (finiteWitness units i (k-weight i)) =
      SourceOpenFractionField318.orderToOpen units
        (algebraMap ℚ (ContactKummerOrder318.SourceOrder units) q * finiteWitness units i (k-weight i)) := by
    rw [map_mul,RingHom.map_rat_algebraMap]
  unfold poleClass
  rw [mul_assoc,pole_of_weight_le units i k hk,hw]
  exact finite_boundary_zero _

/-- Zero-pole classes vanish through the actual infinity-ring image. -/
theorem poleClass_zero_pole (q : ℚ) (i : ThreeIndex) : poleClass q 0 i = 0 := by
  have hw : algebraMap ℚ (ContactKummerOrder318.OpenOrder units) q *
      InfinityOverlapLocalization318.toOpen units (ContactHOneOrderBases318.infinityBasis units i) =
      InfinityOverlapLocalization318.toOpen units
        (algebraMap ℚ (InfinityOpenChart318.OpenOrder units) q * ContactHOneOrderBases318.infinityBasis units i) := by
    rw [map_mul,RingHom.map_rat_algebraMap]
  unfold poleClass
  rw [pow_zero,mul_one,hw]
  exact infinity_boundary_zero _

theorem weight_le_three (i : ThreeIndex) : weight i ≤ 3 := by
  rcases i with ⟨i,⟨j,k⟩⟩
  dsimp [weight]
  omega

/-- The complete candidate domain: positive poles strictly below the ratio
weight. Fin 3 loses nothing since every weight is at most three. -/
abbrev SmallIndex := {p : ThreeIndex × Fin 3 // 0 < p.2.val ∧ p.2.val < weight p.1}

/-- There are exactly five possible surviving monomial indices. This is a
count of candidate representatives, not an independence or spanning theorem. -/
theorem smallIndex_card : Fintype.card SmallIndex = 5 := by decide

theorem small_pole_lt_three (i : ThreeIndex) (k : ℕ) (hk : k < weight i) : k < 3 :=
  lt_of_lt_of_le hk (weight_le_three i)

/-- Every pole outside the declared candidate domain is killed by an original
chart image; no pole order is omitted. -/
theorem poleClass_zero_outside_small (q : ℚ) (k : ℕ) (i : ThreeIndex)
    (hk : ¬ (0 < k ∧ k < weight i)) : poleClass q k i = 0 := by
  by_cases hzero : k = 0
  · subst k
    exact poleClass_zero_pole q i
  · apply poleClass_zero_of_weight_le q k i
    omega

end ActualSourceHOneSmallPoles318
