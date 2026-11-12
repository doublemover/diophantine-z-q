module
public import ActualSelectedOrderModuli318
public section
noncomputable section
namespace ActualOrderPrimeTrace318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- The original selected trace now uses only a fixed prime-size bound and
actual roots, with both moduli constructed, and no local-unit/order-divisibility
or detector-error inputs. Compatibility of these moduli is NOT asserted. -/
theorem selected_trace (a : ℤ) (hn : ∀ j, labels j≠0)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (u w : ℤ) (hp : Values C u w) (r : Roots C u w hp)
    (hlarge : ∀ j : Fin 3, ∀ i : Fin 5, FixedSelectedPrimeBound318.bound C<(row C u w j i).natAbs)
    (h : ℕ)
    (hprimary : Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*minus C u w hp r) h 0)
    (hopposite : Nat.ModEq (plus C u w hp r) h 1)
    (hzero : (h:ℤ)≠0) (hone : (h:ℤ)≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0) :
    SelectedContactDenominators318.SelectedTrace C (a:ℚ) (h:ℤ) u w hp :=
  SelectedTraceFromOrders318.selected_trace C a hn hbeta hlucas h u w hp
    (FixedSelectedPrimeBound318.avoidance C hn u w hp hlarge)
    (minus C u w hp r) (plus C u w hp r) (orders C u w hp r)
    hprimary hopposite hzero hone hg

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- All three ACTUAL pole-preparation predicates, with both the local depth
modulus Q and prime bound fixed BEFORE the prime pattern. The only post-pattern
conditions are the same CRT index/real positivity/guards and actual roots. -/
theorem preparation_family (a : ℤ) (hn : ∀ j, labels j≠0)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (h₀ L : ℕ) (N₂ N₃ N₁₇ : ℤ)
    (h₂ : SourceLocalProgression318.Prepared 2 (a:ℚ) labels h₀ L N₂ 3)
    (h₃ : SourceLocalProgression318.Prepared 3 (a:ℚ) labels h₀ L N₃ 1)
    (h₁₇ : SourceLocalProgression318.Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2) :
    ∃ Q : ℕ, 0<Q ∧ ∀ u w : ℤ, ∀ hp : Values C u w,
      (Q:ℤ)∣w → (∀ k∈coefficients C, (408:ℤ)∣value u w k-1) →
      (∀ j : Fin 3, ∀ i : Fin 5, FixedSelectedPrimeBound318.bound C<(row C u w j i).natAbs) →
      ∀ r : Roots C u w hp, ∀ h : ℕ,
      Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*minus C u w hp r) h 0 →
      Nat.ModEq (plus C u w hp r) h 1 → Nat.ModEq L h h₀ →
      (h:ℤ)≠0 → (h:ℤ)≠1 →
      (∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0) →
      (∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ)
        (parameter C u w) (190+51*j.val) ∧
        ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) (parameter C u w) (190+51*j.val)<17) →
      ThreeSelectedPolePreparation318.Prepared (a:ℚ) labels (h:ℤ) (parameter C u w) := by
  obtain ⟨Q,hQ,hfamily⟩ := ThreeSelectedPolePreparation318.family C hn (a:ℚ)
    h₀ L N₂ N₃ N₁₇ h₂ h₃ h₁₇
  refine ⟨Q,hQ,?_⟩
  intro u w hp hw hray hlarge r h hprimary hopposite hcontinuity hzero hone hg hb
  exact hfamily u w hp hw hray h hcontinuity hb
    (selected_trace C a hn hbeta hlucas u w hp r hlarge h hprimary hopposite hzero hone hg)

end ActualOrderPrimeTrace318
