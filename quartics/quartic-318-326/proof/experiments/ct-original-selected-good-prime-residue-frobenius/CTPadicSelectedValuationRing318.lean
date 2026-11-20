module
public import CTPadicUnramifiedProjectedNorm318
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Valuation.Extension
public section
noncomputable section

namespace CTPadicSelectedValuationRing318

open IsLocalRing
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]
variable {L Γ : Type*} [Field L] [Algebra ℚ_[p] L] [LinearOrderedCommGroupWithZero Γ]

/-- The base ring acts through the native inclusion Z_p → Q_p. The
instance is scoped to avoid changing unrelated local-field algebras. -/
scoped instance padicFieldIntegralAlgebra : Algebra ℤ_[p] L :=
  ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

scoped instance padicFieldIntegralTower : IsScalarTower ℤ_[p] ℚ_[p] L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem padicVal_le_one (x : ℚ_[p]) :
    Padic.mulValuation x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  have h : 1 < ‖x‖ ↔ 1 < Padic.mulValuation x := by
    simpa only [norm_one,map_one] using
      (Padic.norm_lt_norm_iff_mulValuation_lt (x := (1 : ℚ_[p])) (y := x))
  simpa only [not_lt] using h.not.symm

private theorem padicVal_eq_one (x : ℚ_[p]) :
    Padic.mulValuation x = 1 ↔ ‖x‖ = 1 := by
  have h : ‖x‖ < 1 ↔ Padic.mulValuation x < 1 := by
    simpa only [norm_one,map_one] using
      (Padic.norm_lt_norm_iff_mulValuation_lt (x := x) (y := (1 : ℚ_[p])))
  have h' : 1 ≤ Padic.mulValuation x ↔ 1 ≤ ‖x‖ := by
    simpa only [not_lt] using h.not.symm
  simpa only [le_antisymm_iff] using and_congr (padicVal_le_one x) h'

variable (v : Valuation L Γ) [(Padic.mulValuation (p := p)).HasExtension v]

/-- Restriction of the supplied genuine extended valuation detects exactly
the native p-adic norm-one condition without an extra normalization. -/
theorem base_value_one (x : ℚ_[p]) :
    v (algebraMap ℚ_[p] L x) = 1 ↔ ‖x‖ = 1 :=
  (Valuation.HasExtension.val_map_eq_one_iff (Padic.mulValuation (p := p)) v x).trans
    (padicVal_eq_one x)

/-- Canonical base integers action on the literal valuation subring:
do not identify that subring with an independently selected ring. -/
@[expose] def padicIntegerHom : ℤ_[p] →+* v.valuationSubring :=
  (algebraMap ℤ_[p] L).codRestrict v.valuationSubring.toSubring fun x => by
    change v (algebraMap ℚ_[p] L (x : ℚ_[p])) ≤ 1
    apply (Valuation.HasExtension.val_map_le_one_iff (Padic.mulValuation (p := p)) v _).2
    exact (padicVal_le_one (x : ℚ_[p])).2 x.property

scoped instance padicIntegersAlgebra : Algebra ℤ_[p] v.valuationSubring :=
  (padicIntegerHom v).toAlgebra

scoped instance padicIntegersTower : IsScalarTower ℤ_[p] v.valuationSubring L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

scoped instance padicIntegersFaithful : FaithfulSMul ℤ_[p] v.valuationSubring :=
  (faithfulSMul_iff_algebraMap_injective ℤ_[p] v.valuationSubring).2 fun x y h =>
    ((algebraMap ℚ_[p] L).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p]))
      (congrArg Subtype.val h)

scoped instance padicIntegersLocalHom :
    IsLocalHom (algebraMap ℤ_[p] v.valuationSubring) where
  map_nonunit x hx := by
    have hvx := (v.valuationSubring.integers).one_of_isUnit hx
    change v (algebraMap ℚ_[p] L (x : ℚ_[p])) = 1 at hvx
    apply PadicInt.isUnit_iff.2
    simpa only [PadicInt.norm_def] using (base_value_one v _).1 hvx

/-- The mathematical integrality cut is only the forward implication.
The reverse is the pinned valuation integrality theorem, using exactly
the local scalar tower above. -/
theorem actual_isIntegralClosure
    (hInt : ∀ x : L, v x ≤ 1 → IsIntegral ℤ_[p] x) :
    IsIntegralClosure v.valuationSubring ℤ_[p] L where
  algebraMap_injective := ValuationSubring.subtype_injective _
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      have h : IsIntegral v.valuationSubring x := hx.tower_top
      exact v.valuationSubring.integers.exists_of_le_one
        ((v.valuationSubring.integers.isIntegral_iff_v_le_one).1 h)
    · rintro ⟨y,rfl⟩
      exact hInt _ y.property

variable [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-- Same integral basis on the literal valuation ring; no basis witness
is left once that ring has been identified as the integral closure. -/
def actualIntegralBasis [IsIntegralClosure v.valuationSubring ℤ_[p] L] :
    Σ n : ℕ, Basis (Fin n) ℤ_[p] v.valuationSubring := by
  letI : Module.Finite ℤ_[p] v.valuationSubring :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] L v.valuationSubring
  letI : IsTorsionFree ℤ_[p] L := .trans_faithfulSMul ℤ_[p] ℚ_[p] L
  letI : IsTorsionFree ℤ_[p] v.valuationSubring :=
    IsIntegralClosure.isTorsionFree ℤ_[p] L
  exact Module.basisOfFiniteTypeTorsionFree'

/-- Once actual integrality and the literal local maximal-ideal
equality are supplied, the same-layer norm theorem requires no other
local algebra instance, integral basis or formal-unramified assumption. -/
theorem actual_norm_onto_fixed_units
    (hInt : ∀ x : L, v x ≤ 1 → IsIntegral ℤ_[p] x)
    (hI : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] v.valuationSubring) =
      maximalIdeal v.valuationSubring)
    (u : v.valuationSubringˣ)
    (hu : ∀ σ : L ≃ₐ[ℚ_[p]] L, σ (u : v.valuationSubring) = (u : v.valuationSubring)) :
    ∃ w : v.valuationSubringˣ, (∏ σ : L ≃ₐ[ℚ_[p]] L, σ (w : v.valuationSubring)) =
      (u : v.valuationSubring) := by
  letI := actual_isIntegralClosure v hInt
  let ⟨n,b⟩ := actualIntegralBasis v
  obtain ⟨a,ha⟩ := CTPadicUnramifiedProjectedNorm318.fixed_integral_unit_base_preimage
    v v.valuationSubring.integers (base_value_one v) u hu
  obtain ⟨w,hw⟩ := CTPadicUnramifiedProjectedNorm318.actual_unit_galois_product_from_integral_norm b
    (CTPadicUnramifiedProjectedNorm318.unit_norm_surj_of_integral_basis b hI) a
  exact ⟨w,hw.trans ha⟩

end CTPadicSelectedValuationRing318
