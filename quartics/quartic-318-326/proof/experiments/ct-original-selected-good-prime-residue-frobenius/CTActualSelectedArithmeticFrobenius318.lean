module
public import CTActualSelectedResidueGalois318
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup
public section
noncomputable section

namespace CTActualSelectedArithmeticFrobenius318

open CTActualSelectedPadicLayer318 CTActualSelectedPadicValuation318
open CTActualSelectedResidueGalois318
open IsLocalRing
open scoped CTPadicSelectedValuationRing318

variable (p : ℕ) [Fact p.Prime] (M : GlobalLayer)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (Pbar p) Γ) [(Padic.mulValuation (p := p)).HasExtension w]
variable (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField)

local notation "L" => localField p M
local notation "S" => selectedIntegers p M w
local notation "k" => ResidueField ℤ_[p]
local notation "l" => ResidueField S
local notation "GalL" => (L ≃ₐ[ℚ_[p]] L)
local notation "Galbar" => (l ≃ₐ[k] l)
local notation "Dold" => (globalPulledRestriction p M).range

local instance padicResidueFintype : Fintype k :=
  Fintype.ofEquiv (ZMod p) PadicInt.residueField.symm.toEquiv

private theorem base_residue_card : Fintype.card k = p :=
  (Fintype.card_congr PadicInt.residueField.toEquiv).trans (ZMod.card p)

/-- Arithmetic Frobenius raises the residue to its p-th power.
This is not the inverse convention. -/
def arithmeticResidue : Galbar := by
  letI : Finite l := (residue_finite_finrank p M w hD).1
  exact FiniteField.frobeniusAlgEquivOfAlgebraic k l

theorem arithmeticResidue_apply (x : l) :
    arithmeticResidue p M w hD x = x^p := by
  letI : Finite l := (residue_finite_finrank p M w hD).1
  change FiniteField.frobeniusAlgEquivOfAlgebraic k l x = x^p
  rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,base_residue_card p]

def arithmeticFrobenius : GalL :=
  (residueGaloisEquiv p M w hD).symm (arithmeticResidue p M w hD)

theorem arithmeticFrobenius_reduction :
    residueGaloisEquiv p M w hD (arithmeticFrobenius p M w hD) =
      arithmeticResidue p M w hD :=
  (residueGaloisEquiv p M w hD).apply_symm_apply _

theorem arithmeticFrobenius_residue_apply (x : l) :
    residueGaloisEquiv p M w hD (arithmeticFrobenius p M w hD) x = x^p := by
  rw [arithmeticFrobenius_reduction,arithmeticResidue_apply]

/-- In the geometric convention the same automorphism is inverted;
in particular its residue UNDOES the p-power map. -/
def geometricFrobenius : GalL := (arithmeticFrobenius p M w hD)⁻¹

theorem geometricFrobenius_undoes_arithmetic (x : l) :
    residueGaloisEquiv p M w hD (geometricFrobenius p M w hD) (x^p) = x := by
  rw [← arithmeticFrobenius_residue_apply p M w hD x,geometricFrobenius,map_inv]
  exact (residueGaloisEquiv p M w hD (arithmeticFrobenius p M w hD)).symm_apply_apply x

/-- Every actual automorphism is a nonnegative power of the arithmetic
generator. The finite field proof uses the genuinely reduced common
basis, not the cardinality of the full global Galois group. -/
theorem arithmeticFrobenius_generates (σ : GalL) :
    ∃ n : ℕ, (arithmeticFrobenius p M w hD)^n = σ := by
  letI : Finite l := (residue_finite_finrank p M w hD).1
  obtain ⟨n,hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).2
    (residueGaloisEquiv p M w hD σ)
  refine ⟨n.val,(residueGaloisEquiv p M w hD).injective ?_⟩
  rw [map_pow,arithmeticFrobenius_reduction]
  exact hn

/-- Exact comparison for the actual image of the original global
restriction, rather than an independently chosen cyclic quotient. -/
def oldResidueGaloisEquiv : Dold ≃* Galbar :=
  (localGalEquivGlobalImage p M).symm.trans (residueGaloisEquiv p M w hD)

theorem oldResidueGaloisEquiv_on_restriction
    (σ : Field.absoluteGaloisGroup ℚ_[p]) :
    oldResidueGaloisEquiv p M w hD (⟨globalPulledRestriction p M σ,⟨σ,rfl⟩⟩ : Dold) =
      residueGaloisEquiv p M w hD (localRestriction p M σ) := by
  have h : localGalEquivGlobalImage p M (localRestriction p M σ) =
      (⟨globalPulledRestriction p M σ,⟨σ,rfl⟩⟩ : Dold) :=
    Subtype.ext (localGalEquivGlobalImage_on_restriction p M σ)
  change residueGaloisEquiv p M w hD
      ((localGalEquivGlobalImage p M).symm (⟨globalPulledRestriction p M σ,⟨σ,rfl⟩⟩ : Dold)) = _
  rw [← h,MulEquiv.symm_apply_apply]

/-- The generator in the image of the original source-layer
restriction, not an arbitrary choice of an abstract cyclic group. -/
def oldArithmeticFrobenius : Dold :=
  localGalEquivGlobalImage p M (arithmeticFrobenius p M w hD)

theorem oldArithmeticFrobenius_residue_apply (x : l) :
    oldResidueGaloisEquiv p M w hD (oldArithmeticFrobenius p M w hD) x = x^p := by
  change residueGaloisEquiv p M w hD
    ((localGalEquivGlobalImage p M).symm
      (localGalEquivGlobalImage p M (arithmeticFrobenius p M w hD))) x = x^p
  rw [MulEquiv.symm_apply_apply,arithmeticFrobenius_residue_apply]

theorem oldArithmeticFrobenius_generates (g : Dold) :
    ∃ n : ℕ, (oldArithmeticFrobenius p M w hD)^n = g := by
  obtain ⟨n,hn⟩ := arithmeticFrobenius_generates p M w hD
    ((localGalEquivGlobalImage p M).symm g)
  refine ⟨n,?_⟩
  rw [oldArithmeticFrobenius,← map_pow,hn,MulEquiv.apply_symm_apply]

theorem oldArithmeticFrobenius_mem_zpowers (g : Dold) :
    g ∈ Subgroup.zpowers (oldArithmeticFrobenius p M w hD) := by
  obtain ⟨n,hn⟩ := oldArithmeticFrobenius_generates p M w hD g
  rw [← hn]
  exact Subgroup.npow_mem_zpowers _ _

/-- A lift in the original topological G_Qp has the displayed
arithmetic component under BOTH exact restriction maps. No other
prime of M or independent quotient is chosen. -/
theorem lift_old_arithmeticFrobenius :
    ∃ σ : Field.absoluteGaloisGroup ℚ_[p],
      localRestriction p M σ = arithmeticFrobenius p M w hD ∧
      globalPulledRestriction p M σ = (oldArithmeticFrobenius p M w hD).val := by
  obtain ⟨σ,hσ⟩ := localRestriction_surjective p M (arithmeticFrobenius p M w hD)
  refine ⟨σ,hσ,?_⟩
  rw [oldArithmeticFrobenius,← hσ,localGalEquivGlobalImage_on_restriction]

end CTActualSelectedArithmeticFrobenius318
