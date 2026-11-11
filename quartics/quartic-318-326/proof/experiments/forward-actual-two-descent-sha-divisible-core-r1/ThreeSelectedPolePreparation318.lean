module
public import ContactDenominatorModulus318
public section
noncomputable section
namespace ThreeSelectedPolePreparation318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open SelectedContactDenominators318
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The exact three preparation-zero inputs at their literal stored values.
This predicate has no existential rational elliptic-point assertion. -/
@[expose] def Prepared (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (t : ℚ) : Prop :=
  ∀ j : Fin 3,
    let b := ThreeDetectorUniformFamily318.witness q labels h t (190+51*j.val)
    0<b ∧ b<17 ∧ IsSquare b.den ∧
    IsSquare (b:ℚ_[2]) ∧ 3≤padicValRat 2 b ∧
    IsSquare (b:ℚ_[3]) ∧ 1≤padicValRat 3 b ∧
    IsSquare (b:ℚ_[17]) ∧ 2≤padicValRat 17 b

/-- Original neighborhood thresholds are turned into one prior divisibility
request. Genuine Hensel squares come from the original ray, and square reduced
denominators from the actual selected-place trace inputs, all at the sameh. -/
theorem family {labels : Fin 4 → ℤ} (C : Clearing labels) (hn : ∀ j, labels j≠0)
    (q : ℚ) (h₀ L : ℕ) (N₂ N₃ N₁₇ : ℤ)
    (h₂ : SourceLocalProgression318.Prepared 2 q labels h₀ L N₂ 3)
    (h₃ : SourceLocalProgression318.Prepared 3 q labels h₀ L N₃ 1)
    (h₁₇ : SourceLocalProgression318.Prepared 17 q labels h₀ L N₁₇ 2) :
    ∃ Q : ℕ, 0<Q ∧ ∀ u w : ℤ, ∀ hp : Values C u w,
      (Q:ℤ)∣w → (∀ k∈coefficients C, (408:ℤ)∣value u w k-1) →
      ∀ h : ℕ, Nat.ModEq L h h₀ →
      (∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness q labels (h:ℤ)
        (parameter C u w) (190+51*j.val) ∧
        ThreeDetectorUniformFamily318.witness q labels (h:ℤ) (parameter C u w) (190+51*j.val)<17) →
      SelectedTrace C q (h:ℤ) u w hp → Prepared q labels (h:ℤ) (parameter C u w) := by
  obtain ⟨Q,hQ,hdepth⟩ := ContactDenominatorModulus318.common C N₂ N₃ N₁₇
  refine ⟨Q,hQ,?_⟩
  intro u w hp hw hray h hh hb htrace
  obtain ⟨hd₂,hd₃,hd₁₇⟩ := hdepth w hp.nonzero hw
  have hlocal (k : ℤ) (hk : k∈coefficients C) := ContactSmallPrimeRays318.ray_preparation _ (hray k hk)
  have hsmall₂ := local_preparation C 2 q h₀ L h N₂ 3 h₂ u w hp hd₂ hh
    (fun k hk => (hlocal k hk).1) (fun k hk => (hlocal k hk).2.1)
  have hsmall₃ := local_preparation C 3 q h₀ L h N₃ 1 h₃ u w hp hd₃ hh
    (fun k hk => (hlocal k hk).2.2.1) (fun k hk => (hlocal k hk).2.2.2.1)
  have hsmall₁₇ := local_preparation C 17 q h₀ L h N₁₇ 2 h₁₇ u w hp hd₁₇ hh
    (fun k hk => (hlocal k hk).2.2.2.2.1) (fun k hk => (hlocal k hk).2.2.2.2.2)
  have hden := square_denominators C hn q (h:ℤ) u w hp (fun j => (hb j).1) htrace
  intro j
  exact ⟨(hb j).1,(hb j).2,hden j,(hsmall₂ j).1,(hsmall₂ j).2,
    (hsmall₃ j).1,(hsmall₃ j).2,(hsmall₁₇ j).1,(hsmall₁₇ j).2⟩

end ThreeSelectedPolePreparation318
