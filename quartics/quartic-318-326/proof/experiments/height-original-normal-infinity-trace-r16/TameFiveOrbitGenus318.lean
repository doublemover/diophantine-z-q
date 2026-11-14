module
public import FiveOrbitGenusSqueeze318
public section
noncomputable section
namespace TameFiveOrbitGenus318
open MulAction FiveOrbitGenusSqueeze318
variable {G Ω k : Type*} [Group G] [Fintype G] [Fintype Ω]
  [MulAction G Ω] [Field k]

/-- Genuine tangent actions and nontrivial inertia derive every orbit size;
only the geometric upper bound and original Riemann--Hurwitz remain supplied. -/
theorem original_branch_exhaustion (hG : Fintype.card G = 16)
    (hchar : (2 : k) ≠ 0) (hperiod : ∀ g : G, g * g = 1)
    (A : ∀ x : Ω, FormalStabilizer318.Action (stabilizer G x) k)
    (hbranch : ∀ x : Ω, ∃ g : G, g ≠ 1 ∧ g • x = x)
    (point : Fin 5 → Ω)
    (hpoint : Function.Injective (fun i => orbitClass (G := G) (point i)))
    (sourceGenus quotientGenus : ℕ) (hupper : sourceGenus ≤ 5)
    (hRH : 2 * (sourceGenus : ℤ) - 2 = 16 * (2 * (quotientGenus : ℤ) - 2) +
      ((∑ g : {g : G // g ≠ 1}, Nat.card (fixedBy Ω g.val)) : ℕ)) :
    sourceGenus = 5 ∧ quotientGenus = 0 ∧ Fintype.card Ω = 40 ∧
      Function.Bijective (fun i => orbitClass (G := G) (point i)) := by
  rw [FiveBranchCount318.nonidentity_fixed_sum hchar hperiod A hbranch] at hRH
  have ho := FiveBranchCount318.branch_orbit_card_eight hG hchar hperiod A hbranch
  have hg := genus_and_count ho point hpoint sourceGenus quotientGenus hupper hRH
  exact ⟨hg.1, hg.2.1, hg.2.2.1,
    displayed_bijective ho point hpoint sourceGenus quotientGenus hupper hRH⟩

/-- An actual unramified covering from a genus-five polygon surface must
have degree one once the same target's genus upper bound is saturated.
This is the numerical consequence of the actual covering Euler identity,
not a construction of that polygon or covering. -/
theorem covering_degree_one (genus degree : ℕ) (hgenus : genus = 5)
    (hcover : (8 : ℤ) = (degree : ℤ) * (2 * (genus : ℤ) - 2)) : degree = 1 := by
  subst genus
  norm_num at hcover
  omega
end TameFiveOrbitGenus318
