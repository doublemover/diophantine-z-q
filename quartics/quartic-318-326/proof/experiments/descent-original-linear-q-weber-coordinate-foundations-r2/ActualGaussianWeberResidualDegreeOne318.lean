module
public import ActualGaussianWeberNormalizedAbscissaDegree318
public import ActualGaussianWeberRelativeFrobFactor318
public import Mathlib.RingTheory.Coprime.Lemmas
public section
noncomputable section

namespace ActualGaussianWeberResidualDegreeOne318

open Polynomial
open ActualGaussianWeberNormalizedAbscissaDegree318
open ActualGaussianWeberRelativeFrobFactor318

variable {k F : Type*} [Field k] [Field F]

/-- When the actual embedded quotient is nonconstant, its two
polynomials cannot both have degree zero. No transcendence or pole
assumption is needed for this last normalization implication. -/
theorem positive_abscissa_height (f : k[X] →+* F) {A B : k[X]}
    (hn : ∀ c : k, f A/f B ≠ f (C c)) :
    0 < max A.natDegree B.natDegree := by
  by_contra h
  have hA : A.natDegree = 0 := by
    have hl := le_max_left A.natDegree B.natDegree
    omega
  have hB : B.natDegree = 0 := by
    have hr := le_max_right A.natDegree B.natDegree
    omega
  have hAa : f A = f (C (A.coeff 0)) := congrArg f (eq_C_of_natDegree_eq_zero hA)
  have hBb : f B = f (C (B.coeff 0)) := congrArg f (eq_C_of_natDegree_eq_zero hB)
  apply hn (A.coeff 0 / B.coeff 0)
  calc
    _ = f (C (A.coeff 0)) / f (C (B.coeff 0)) := congrArg₂ (· / ·) hAa hBb
    _ = _ := by
      simpa only [RingHom.comp_apply] using
        (map_div₀ (f.comp C) (A.coeff 0) (B.coeff 0)).symm

variable {p : ℕ} [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP F p]

/-- Exact coordinate result after a stationary genuine coprime
abscissa, a degree cap on both coordinates of that fraction, and
a nonconstant image. The two selected polynomial roots are used
both in the degree result and in the actual point preimage. -/
theorem degree_one_cubic_factor (hodd : Odd p)
    (f : k[X] →+* F) {A B : k[X]} (v : F)
    (hAB : IsCoprime A B) (hA : A.derivative = 0) (hB : B.derivative = 0)
    (hDen : f B ≠ 0) (hNC : ∀ c : k, f A/f B ≠ f (C c))
    (hCap : max A.natDegree B.natDegree ≤ p)
    (hCubic : v^2 = (f A/f B)^3 - (f A/f B)) :
    ∃ A₁ B₁ : k[X], ∃ V : F,
      A₁^p=A ∧ B₁^p=B ∧ f B₁≠0 ∧ IsCoprime A₁ B₁ ∧
      max A₁.natDegree B₁.natDegree=1 ∧
      (f A₁/f B₁)^p=f A/f B ∧ V^p=v ∧
      V^2=(f A₁/f B₁)^3-(f A₁/f B₁) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨A₁,hAp⟩ := polynomial_pth_root A hA
  obtain ⟨B₁,hBp⟩ := polynomial_pth_root B hB
  have hDen₁ : f B₁ ≠ 0 := by
    intro hu
    apply hDen
    rw [←hBp,map_pow,hu,zero_pow hp.ne']
  have hk : IsCoprime (A₁^p) (B₁^p) := by
    rw [hAp,hBp]
    exact hAB
  have hk₁ : IsCoprime A₁ B₁ := (IsCoprime.pow_iff hp hp).mp hk
  have hPos := positive_abscissa_height f hNC
  obtain ⟨hA₁,hB₁,hEq⟩ := root_degrees_one_of_nonconstant_cap hp hAp hBp hPos hCap
  have hd : max A₁.natDegree B₁.natDegree = 1 := by
    apply le_antisymm (max_le_iff.mpr ⟨hA₁,hB₁⟩)
    rcases hEq with h | h
    · exact h.symm.le.trans (le_max_left _ _)
    · exact h.symm.le.trans (le_max_right _ _)
  have hU : (f A₁/f B₁)^p = f A/f B := by
    calc
      _ = f (A₁^p) / f (B₁^p) := by simp only [div_pow,map_pow]
      _ = _ := by rw [hAp,hBp]
  obtain ⟨V,hV,hWV⟩ := cubic_coordinates_pth_roots hodd hU hCubic
  exact ⟨A₁,B₁,V,hAp,hBp,hDen₁,hk₁,hd,hU,hV,hWV⟩

end ActualGaussianWeberResidualDegreeOne318
