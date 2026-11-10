module
public import FiveBranchCount318
public section
noncomputable section
open scoped BigOperators
namespace FiveOrbitGenusSqueeze318
open MulAction
variable {G Ω : Type*} [Group G] [Fintype Ω] [MulAction G Ω]

/-- Exact numerical squeeze with nonnegative genera and the full branch count. -/
theorem numerical (sourceGenus quotientGenus branchCount total : ℕ)
    (hupper : sourceGenus ≤ 5) (hknown : 5 ≤ branchCount)
    (htotal : total = branchCount * 8)
    (hRH : 2 * (sourceGenus : ℤ) - 2 =
      16 * (2 * (quotientGenus : ℤ) - 2) + (total : ℤ)) :
    sourceGenus = 5 ∧ quotientGenus = 0 ∧ total = 40 ∧ branchCount = 5 := by
  omega

/-- The original orbit quotient, with no independently chosen branch set. -/
@[expose] def orbitClass (x : Ω) : Quotient (orbitRel G Ω) := Quotient.mk'' x

/-- Count the WHOLE original finite ramification locus by its actual orbits. -/
theorem total_of_orbits (horbit : ∀ x : Ω, Nat.card (orbit G x) = 8) :
    Fintype.card Ω = Nat.card (Quotient (orbitRel G Ω)) * 8 := by
  classical
  letI : Fintype (Quotient (orbitRel G Ω)) := Fintype.ofFinite _
  letI : (x : Ω) → Fintype (orbit G x) := fun _ => Fintype.ofFinite _
  have he := Fintype.card_congr (MulAction.selfEquivSigmaOrbits G Ω)
  rw [Fintype.card_sigma] at he
  have ho : ∀ x : Ω, Fintype.card (orbit G x) = 8 := by
    intro x
    simpa only [Nat.card_eq_fintype_card] using horbit x
  simp_rw [ho] at he
  simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card] using he

/-- Five distinct displayed orbits plus source genus AT MOST five force the
source genus, quotient genus and entire ramification count. The actual
Riemann--Hurwitz identity is retained as a geometric input. -/
theorem genus_and_count (horbit : ∀ x : Ω, Nat.card (orbit G x) = 8)
    (point : Fin 5 → Ω) (hpoint : Function.Injective (fun i => orbitClass (G := G) (point i)))
    (sourceGenus quotientGenus : ℕ) (hupper : sourceGenus ≤ 5)
    (hRH : 2 * (sourceGenus : ℤ) - 2 =
      16 * (2 * (quotientGenus : ℤ) - 2) + (Fintype.card Ω : ℤ)) :
    sourceGenus = 5 ∧ quotientGenus = 0 ∧ Fintype.card Ω = 40 ∧
      Nat.card (Quotient (orbitRel G Ω)) = 5 := by
  have htotal := total_of_orbits horbit
  have hlower : 5 ≤ Nat.card (Quotient (orbitRel G Ω)) := by
    simpa using Nat.card_le_card_of_injective _ hpoint
  exact numerical sourceGenus quotientGenus _ _ hupper hlower htotal hRH

/-- The five original displayed orbit classes are a bijection, not merely
five abstract slots with the correct cardinality. -/
theorem displayed_bijective (horbit : ∀ x : Ω, Nat.card (orbit G x) = 8)
    (point : Fin 5 → Ω) (hpoint : Function.Injective (fun i => orbitClass (G := G) (point i)))
    (sourceGenus quotientGenus : ℕ) (hupper : sourceGenus ≤ 5)
    (hRH : 2 * (sourceGenus : ℤ) - 2 =
      16 * (2 * (quotientGenus : ℤ) - 2) + (Fintype.card Ω : ℤ)) :
    Function.Bijective (fun i => orbitClass (G := G) (point i)) := by
  classical
  letI : Fintype (Quotient (orbitRel G Ω)) := Fintype.ofFinite _
  have hc := (genus_and_count horbit point hpoint sourceGenus quotientGenus hupper hRH).2.2.2
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨hpoint, by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hc.symm⟩

/-- Every branch orbit has exactly one of the ORIGINAL displayed labels. -/
theorem displayed_exhaustion (horbit : ∀ x : Ω, Nat.card (orbit G x) = 8)
    (point : Fin 5 → Ω) (hpoint : Function.Injective (fun i => orbitClass (G := G) (point i)))
    (sourceGenus quotientGenus : ℕ) (hupper : sourceGenus ≤ 5)
    (hRH : 2 * (sourceGenus : ℤ) - 2 =
      16 * (2 * (quotientGenus : ℤ) - 2) + (Fintype.card Ω : ℤ)) (x : Ω) :
    ∃! i : Fin 5, orbitClass (G := G) (point i) = orbitClass (G := G) x := by
  have hb := displayed_bijective horbit point hpoint sourceGenus quotientGenus hupper hRH
  obtain ⟨i, hi⟩ := hb.2 (orbitClass (G := G) x)
  exact ⟨i, hi, fun j hj => hb.1 (hj.trans hi.symm)⟩
end FiveOrbitGenusSqueeze318
