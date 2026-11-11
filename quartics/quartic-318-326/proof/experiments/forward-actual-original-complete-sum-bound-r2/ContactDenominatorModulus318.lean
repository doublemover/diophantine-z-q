module
public import ContactSmallPrimeRays318
public section
noncomputable section
namespace ContactDenominatorModulus318
open ClearedContactForms318 ContactPatternSupport318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

lemma depth_of_dvd (p : ℕ) [Fact p.Prime] (N : ℤ) (w : ℤ) (hw : w≠0)
    (hdiv : (p:ℤ)^N.natAbs∣w) : N≤padicValRat p (denominator C w) := by
  have hdepth : N.natAbs≤padicValInt p w := by
    rcases (padicValInt_dvd_iff N.natAbs w).mp hdiv with hz|hv
    · exact False.elim (hw hz)
    · exact hv
  have hN : N≤(N.natAbs:ℤ) := by rw [Int.natCast_natAbs]; exact le_abs_self _
  have hD : (C.denominator:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt C.positive
  have hwQ : (w:ℚ)≠0 := by exact_mod_cast hw
  have hnonneg : 0≤padicValRat p (C.denominator:ℚ) := by
    rw [padicValRat.of_nat]
    exact_mod_cast Nat.zero_le (padicValNat p C.denominator)
  rw [denominator,padicValRat.mul hD hwQ,padicValRat.of_int]
  omega

/-- One explicit divisibility request for w enforces all three local
thresholds. It is chosen before prime selection and imposes no coprimality
between the local moduli. The denominator D already fixed by labels is kept. -/
theorem common (N₂ N₃ N₁₇ : ℤ) :
    ∃ Q : ℕ, 0<Q ∧ ∀ w : ℤ, w≠0 → (Q:ℤ)∣w →
      N₂≤padicValRat 2 (denominator C w) ∧
      N₃≤padicValRat 3 (denominator C w) ∧
      N₁₇≤padicValRat 17 (denominator C w) := by
  let Q := 2^N₂.natAbs*3^N₃.natAbs*17^N₁₇.natAbs
  have h2 : 2^N₂.natAbs∣Q := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  have h3 : 3^N₃.natAbs∣Q := dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have h17 : 17^N₁₇.natAbs∣Q := dvd_mul_left _ _
  refine ⟨Q,by dsimp [Q]; positivity,?_⟩
  intro w hw hQ
  have h2Z : (2:ℤ)^N₂.natAbs∣(Q:ℤ) := by exact_mod_cast h2
  have h3Z : (3:ℤ)^N₃.natAbs∣(Q:ℤ) := by exact_mod_cast h3
  have h17Z : (17:ℤ)^N₁₇.natAbs∣(Q:ℤ) := by exact_mod_cast h17
  exact ⟨depth_of_dvd C 2 N₂ w hw (h2Z.trans hQ),
    depth_of_dvd C 3 N₃ w hw (h3Z.trans hQ),
    depth_of_dvd C 17 N₁₇ w hw (h17Z.trans hQ)⟩

end ContactDenominatorModulus318
