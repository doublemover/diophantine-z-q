module
public import CTActualSelectedOrderFraction318
public import CTPadicAdicFiniteComplete318
public import CTHenselianFiniteIdempotent318
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.GoingUp
import all Mathlib.RingTheory.Localization.Basic
public section
noncomputable section

namespace CTActualSelectedImageOrderLocal318

open CTActualSelectedPadicLayer318 CTActualSelectedPadicValuation318
open CTActualSelectedImageOrder318 CTActualSelectedOrderFraction318
open IsLocalRing
open scoped CTPadicSelectedValuationRing318 BigOperators

variable (p : ℕ) [Fact p.Prime] (M : GlobalLayer)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (Pbar p) Γ) [(Padic.mulValuation (p := p)).HasExtension w]

local notation "R" => ℤ_[p]
local notation "L" => localField p M
local notation "S" => selectedIntegers p M w
local notation "B" => imageOrder p M w
local notation "q" => imageOrderPrime p M w
local notation "D" => localOrder p M w

/-- The literal finite image ring inherits ideal-adic completeness
from the p-adic integers, then has only one Artinian local factor
because it is a domain. No discriminant assumption is needed here. -/
theorem imageOrder_isLocalRing : IsLocalRing B := by
  let I := maximalIdeal R
  let J := I.map (algebraMap R B)
  letI : IsAdicComplete I R := CTPadicAdicFiniteComplete318.padic_adic_complete p
  letI : IsAdicComplete I B := CTPadicAdicFiniteComplete318.finite_module_complete I
  letI : IsAdicComplete J B := (IsAdicComplete.map_algebraMap_iff (M := B)).2 inferInstance
  let k := ResidueField R
  letI : Algebra k (B ⧸ J) := inferInstanceAs (Algebra (R ⧸ I) (B ⧸ J))
  letI : IsScalarTower R k (B ⧸ J) := inferInstanceAs (IsScalarTower R (R ⧸ I) (B ⧸ J))
  letI : Module.Finite k (B ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R k (B ⧸ J)
  letI : IsArtinianRing (B ⧸ J) := IsArtinianRing.of_finite k (B ⧸ J)
  exact CTHenselianFiniteIdempotent318.domain_local_of_henselian_artinian_quotient B J

theorem imageOrderPrime_isMaximal : q.IsMaximal := by
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q
  have h : q.under R = maximalIdeal R := by
    change ((maximalIdeal S).comap B.val.toRingHom).comap (algebraMap R B) = _
    rw [Ideal.comap_comap,B.val.comp_algebraMap]
    exact IsLocalRing.maximalIdeal_comap (algebraMap R S)
  rw [h]
  exact maximalIdeal.isMaximal _

/-- Localizing this particular finite image order at q is the identity,
because after the actual localness theorem every denominator is a unit. -/
theorem imageOrder_to_localOrder_surjective :
    Function.Surjective (algebraMap B D) := by
  letI : IsLocalRing B := imageOrder_isLocalRing p M w
  have hq : q = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (imageOrderPrime_isMaximal p M w)
  have hU : q.primeCompl ≤ IsUnit.submonoid B := by
    intro x hx
    change IsUnit x
    apply IsLocalRing.notMem_maximalIdeal.1
    rw [← hq]
    exact hx
  exact (IsLocalization.atUnits B q.primeCompl (S := D) hU).surjective

/-- The original, finite order itself embeds onto the same valuation
subring; no "finite localization" shortcut. The discriminant is used
only in identifying the earlier local DVR with the valuation ring. -/
theorem imageOrder_to_selected_surjective
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField) :
    Function.Surjective B.val := by
  intro x
  obtain ⟨y,hy⟩ := localOrderToSelected_surjective p M w hD x
  obtain ⟨z,rfl⟩ := imageOrder_to_localOrder_surjective p M w y
  exact ⟨z,(localOrderToSelected_on_order p M w z).symm.trans hy⟩

theorem selected_forward_integral
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField)
    (x : L) (hx : w (x : Pbar p) ≤ 1) : IsIntegral R x := by
  let y : S := ⟨x,hx⟩
  obtain ⟨z,hz⟩ := imageOrder_to_selected_surjective p M w hD y
  have hZ : IsIntegral R z := Algebra.IsIntegral.isIntegral _
  let f : B →ₐ[R] L := (Algebra.algHom R S L).comp B.val
  have hfx : f z = x := by
    change algebraMap S L (B.val z) = x
    rw [hz] <;> rfl
  rw [← hfx]
  exact hZ.map f

/-- Good-prime unit norm now consumes both conclusions just produced
on the same valuation ring, with no independently supplied integral
basis, forward integrality or maximal-ideal equality. -/
theorem selected_goodPrime_unit_norm
    (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField)
    (u : Sˣ)
    (hu : ∀ σ : L ≃ₐ[ℚ_[p]] L, σ (u : S) = (u : S)) :
    ∃ z : Sˣ, (∏ σ : L ≃ₐ[ℚ_[p]] L, σ (z : S)) = (u : S) :=
  selected_actual_unit_norm p M w (selected_forward_integral p M w hD)
    (actual_maximalIdeal_map p M w hD) u hu

end CTActualSelectedImageOrderLocal318
