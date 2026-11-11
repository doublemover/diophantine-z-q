module
public import ActualFiniteOrbitAccess318
public section
noncomputable section
namespace OriginalNineChartAccess318
open ActualOrbitLocalFilter318 ActualFiniteOrbitAccess318
open scoped Topology
set_option maxHeartbeats 1000000
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Precisely the original four label*h charts, four label*(h−1) charts,
and the common h chart consumed by source compression, in that order. -/
@[expose] def parameters (labels : Fin 4 → ℤ) (h : ℤ) : Fin 9 → ℤ :=
  Fin.append (CoherentMultiplePrefix318.parameters labels h) (fun _ : Fin 1 => h)
@[expose] def intercept (labels : Fin 4 → ℤ) : Fin 9 → ℤ :=
  Fin.append (Fin.append (fun _ : Fin 4 => 0) (fun j => -labels j)) (fun _ : Fin 1 => 0)
@[expose] def slope (labels : Fin 4 → ℤ) : Fin 9 → ℤ :=
  Fin.append (Fin.append labels labels) (fun _ : Fin 1 => 1)
@[expose] def charts (p : ℕ) [Fact p.Prime] (labels : Fin 4 → ℤ) (h : ℤ) : Fin 9 → Fin 4 → ℚ_[p] :=
  fun i => error p (parameters labels h i)

lemma parameter_affine (labels : Fin 4 → ℤ) (h : ℤ) (i : Fin 9) :
    parameters labels h i=intercept labels i+slope labels i*h := by
  fin_cases i <;> simp [parameters,CoherentMultiplePrefix318.parameters,intercept,slope] <;> ring
lemma charts_family (p : ℕ) [Fact p.Prime] (labels : Fin 4 → ℤ) (h : ℤ) :
    charts p labels h=family p (intercept labels) (slope labels) h := by
  ext i j
  rw [charts,parameter_affine]
  rfl

lemma power_modulus_dvd_left (e f : ℕ) : 4*6^e∣4*6^(e+f) := by
  refine ⟨6^f,?_⟩
  rw [pow_add]
  ring
lemma power_modulus_dvd_right (e f : ℕ) : 4*6^f∣4*6^(e+f) := by
  simpa only [Nat.add_comm] using power_modulus_dvd_left f e

/-- One explicitly shaped residue modulus simultaneously accesses any
prescribed open neighborhoods of all nine actual charts at both small places.
All labels, centers and neighborhoods precede the modulus and later h. -/
theorem simultaneous (labels : Fin 4 → ℤ) (h₀ : ℕ)
    (U₂ : Set (Fin 9 → Fin 4 → ℚ_[2])) (U₃ : Set (Fin 9 → Fin 4 → ℚ_[3]))
    (hU₂ : IsOpen U₂) (hU₃ : IsOpen U₃)
    (hc₂ : charts 2 labels (h₀:ℤ)∈U₂) (hc₃ : charts 3 labels (h₀:ℤ)∈U₃) :
    ∃ E : ℕ, 0<4*6^E ∧ ∀ h : ℕ, Nat.ModEq (4*6^E) h h₀ →
      charts 2 labels (h:ℤ)∈U₂ ∧ charts 3 labels (h:ℤ)∈U₃ := by
  rw [charts_family] at hc₂ hc₃
  obtain ⟨e₂,_,he₂⟩ := ActualFiniteOrbitAccess318.two_progression
    (intercept labels) (slope labels) h₀ U₂ hU₂ hc₂
  obtain ⟨e₃,_,he₃⟩ := ActualFiniteOrbitAccess318.three_progression
    (intercept labels) (slope labels) h₀ U₃ hU₃ hc₃
  refine ⟨e₂+e₃,by positivity,?_⟩
  intro h hh
  rw [charts_family,charts_family]
  exact ⟨he₂ h (hh.of_dvd (power_modulus_dvd_left e₂ e₃)),
    he₃ h (hh.of_dvd (power_modulus_dvd_right e₂ e₃))⟩

/-- Additional previously fixed congruences are retained by multiplying
rather than replacing their modulus. This is ready for the original mixed CRT. -/
theorem with_external_modulus (labels : Fin 4 → ℤ) (h₀ M : ℕ) (hM : 0<M)
    (U₂ : Set (Fin 9 → Fin 4 → ℚ_[2])) (U₃ : Set (Fin 9 → Fin 4 → ℚ_[3]))
    (hU₂ : IsOpen U₂) (hU₃ : IsOpen U₃)
    (hc₂ : charts 2 labels (h₀:ℤ)∈U₂) (hc₃ : charts 3 labels (h₀:ℤ)∈U₃) :
    ∃ L : ℕ, 0<L ∧ M∣L ∧ ∀ h : ℕ, Nat.ModEq L h h₀ →
      Nat.ModEq M h h₀ ∧ charts 2 labels (h:ℤ)∈U₂ ∧ charts 3 labels (h:ℤ)∈U₃ := by
  obtain ⟨E,hE,he⟩ := simultaneous labels h₀ U₂ U₃ hU₂ hU₃ hc₂ hc₃
  refine ⟨M*(4*6^E),Nat.mul_pos hM hE,dvd_mul_right _ _,?_⟩
  intro h hh
  exact ⟨hh.of_dvd (dvd_mul_right _ _),he h (hh.of_dvd (dvd_mul_left _ _))⟩

end OriginalNineChartAccess318
