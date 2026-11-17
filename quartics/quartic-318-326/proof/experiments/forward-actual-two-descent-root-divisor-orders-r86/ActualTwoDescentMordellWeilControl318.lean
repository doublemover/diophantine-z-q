module
public import ActualTwoDescentInfiniteGroupBetaPoint318
public section
noncomputable section
namespace ActualTwoDescentMordellWeilControl318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentActualQuotientControl318
open ActualTwoDescentActualMordellWeilStructure318 ActualTwoDescentInfiniteGroupBetaPoint318
open ActualTwoDescentPointExtraction318

/-- This uses the free integer factor in an actual decomposition, NOT
Mathlib's Group.rank (minimal number of arbitrary group generators). -/
def FreeRankAtMostOne (n : ℚ) : Prop :=
  ∃ r : ℕ, r ≤ 1 ∧ ∃ (T : Type) (_ : AddCommGroup T) (_ : Finite T),
    Nonempty (Point n ≃+ (Fin r →₀ ℤ) × T)

def MordellWeilControl (n b : ℕ) : Prop :=
  QuotientControl n b ∧ AddGroup.FG (Point (n : ℚ)) ∧
  Finite (AddCommGroup.torsion (Point (n : ℚ))) ∧ FreeRankAtMostOne (n : ℚ) ∧
  (Infinite (Point (n : ℚ)) → Nonempty (KummerPoint (b : ℚ) (n : ℚ)))

/-- All finite-generation, finite-torsion and upper-rank ingredients are
produced from the actual constructed arithmetic data. -/
theorem actual_mordell_weil_control (n b : ℕ) (hn : n ≠ 0) (C : QuotientControl n b) :
    MordellWeilControl n b := by
  obtain ⟨hfg,hT⟩ := actual_control_finite_generation n b hn C
  obtain ⟨r,hr,T,hgroup,hfin,he,hcard⟩ := actual_free_rank_at_most_one
    (n : ℚ) (by exact_mod_cast hn) C.2.1 C.2.2.1
  exact ⟨C,hfg,hT,⟨r,hr,T,hgroup,hfin,he⟩,actual_beta_point_of_infinite n b hn C⟩

end ActualTwoDescentMordellWeilControl318
