module
public import ActualOrbitTranslatedAccess318
public section
noncomputable section
namespace ActualFiniteOrbitAccess318
open ActualOrbitLocalFilter318
open scoped Topology
set_option maxHeartbeats 1000000

/-- Arbitrarily many original affine index functions are prepared together.
This includes the common h and all fixed-label translates with either sign. -/
@[expose] def family (p : ℕ) [Fact p.Prime] {ι : Type*}
    (a b : ι → ℤ) (h : ℤ) : ι → Fin 4 → ℚ_[p] :=
  fun i => error p (a i+b i*h)

lemma factor_power (e E : ℕ) (he : e≤E) (b m : ℤ) :
    b*(4*(6:ℤ)^E*m)=4*6^e*(6^(E-e)*b*m) := by
  have hp : (6:ℤ)^E=6^e*6^(E-e) := by
    rw [←pow_add,Nat.add_sub_of_le he]
  rw [hp]
  ring

/-- A common exponent is chosen before every later integer multiplier,
with the actual finite-product topology rather than separate existential h's. -/
theorem access (p : ℕ) [Fact p.Prime]
    (hb : ∀ e : ℕ, ∀ m : ℤ, ‖error p (4*6^e*m)‖≤((p:ℝ)⁻¹)^e)
    {ι : Type*} [Fintype ι] (a b : ι → ℤ) (h₀ : ℤ)
    (U : Set (ι → Fin 4 → ℚ_[p])) (hU : IsOpen U) (hcenter : family p a b h₀∈U) :
    ∃ E : ℕ, ∀ m : ℤ, family p a b (h₀+4*6^E*m)∈U := by
  classical
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU (family p a b h₀) hcenter
  have hi : ∀ i : ι, ∃ e : ℕ, ∀ m : ℤ,
      error p (a i+b i*h₀+4*6^e*m)∈Metric.ball (error p (a i+b i*h₀)) ε := by
    intro i
    exact ActualOrbitTranslatedAccess318.access p hb (a i+b i*h₀)
      (Metric.ball _ ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  choose e he using hi
  let E := ∑ i : ι, e i
  have heE (i : ι) : e i≤E := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨E,fun m => hball ?_⟩
  rw [Metric.mem_ball,dist_eq_norm]
  apply (pi_norm_lt_iff hε).mpr
  intro i
  have hm := he i ((6:ℤ)^(E-e i)*b i*m)
  rw [Metric.mem_ball,dist_eq_norm] at hm
  have hindex : a i+b i*(h₀+4*(6:ℤ)^E*m)=
      a i+b i*h₀+4*6^(e i)*(6^(E-e i)*b i*m) := by
    rw [mul_add,factor_power (e i) E (heE i)]
    ring
  simpa only [Pi.sub_apply,family,hindex] using hm

/-- Convert the constructed modulus into the same Nat.ModEq convention
used by mixed CRT. No restriction to h≥h₀ and no negative-multiplier omission. -/
theorem progression (p : ℕ) [Fact p.Prime]
    (hb : ∀ e : ℕ, ∀ m : ℤ, ‖error p (4*6^e*m)‖≤((p:ℝ)⁻¹)^e)
    {ι : Type*} [Fintype ι] (a b : ι → ℤ) (h₀ : ℕ)
    (U : Set (ι → Fin 4 → ℚ_[p])) (hU : IsOpen U) (hcenter : family p a b (h₀:ℤ)∈U) :
    ∃ E : ℕ, 0<4*6^E ∧ ∀ h : ℕ, Nat.ModEq (4*6^E) h h₀ → family p a b (h:ℤ)∈U := by
  obtain ⟨E,hE⟩ := access p hb a b (h₀:ℤ) U hU hcenter
  refine ⟨E,by positivity,?_⟩
  intro h hh
  obtain ⟨m,hm⟩ := Nat.modEq_iff_dvd.mp hh.symm
  have he : (h:ℤ)=(h₀:ℤ)+4*(6:ℤ)^E*m := by
    push_cast at hm
    linarith
  rw [he]
  exact hE m

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
theorem two_progression {ι : Type*} [Fintype ι] (a b : ι → ℤ) (h₀ : ℕ)
    (U : Set (ι → Fin 4 → ℚ_[2])) (hU : IsOpen U) (hcenter : family 2 a b (h₀:ℤ)∈U) :
    ∃ E : ℕ, 0<4*6^E ∧ ∀ h : ℕ, Nat.ModEq (4*6^E) h h₀ → family 2 a b (h:ℤ)∈U :=
  progression 2 two_error_bound a b h₀ U hU hcenter

theorem three_progression {ι : Type*} [Fintype ι] (a b : ι → ℤ) (h₀ : ℕ)
    (U : Set (ι → Fin 4 → ℚ_[3])) (hU : IsOpen U) (hcenter : family 3 a b (h₀:ℤ)∈U) :
    ∃ E : ℕ, 0<4*6^E ∧ ∀ h : ℕ, Nat.ModEq (4*6^E) h h₀ → family 3 a b (h:ℤ)∈U :=
  progression 3 three_error_bound a b h₀ U hU hcenter

end ActualFiniteOrbitAccess318
