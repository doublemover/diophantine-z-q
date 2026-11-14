module
public import ContactArithmeticOriginalSource318
public import SectionHeight318
public section
noncomputable section
namespace IntegralUnitPairNorm318
set_option maxHeartbeats 500000
variable {A K : Type*} [CommRing A] [Field K]
  (φ : A →+* K) (v : AbsoluteValue K ℝ)
  (hφ : ∀ a : A, v (φ a)≤1)

include hφ in
/-- A unit in the actual integral coefficient ring has norm exactly one.
The inverse is evaluated by the same ring hom; no chosen local metric enters. -/
theorem unit_norm (a : A) (ha : IsUnit a) : v (φ a)=1 := by
  obtain ⟨u,rfl⟩ := ha
  have hm : v (φ (u:A))*v (φ ((u⁻¹:Aˣ):A))=1 := by
    rw [←map_mul,←map_mul,Units.mul_inv,map_one,map_one]
  apply le_antisymm (hφ u)
  calc
    1 = v (φ (u:A))*v (φ ((u⁻¹:Aˣ):A)) := hm.symm
    _ ≤ v (φ (u:A))*1 := mul_le_mul_of_nonneg_left (hφ _) (v.nonneg _)
    _ = v (φ (u:A)) := mul_one _

include hφ in
/-- Primitive actual chart coefficients have maximum norm exactly one. -/
theorem pair_max (a0 a1 : A) (hu : IsUnit a0 ∨ IsUnit a1) :
    max (v (φ a0)) (v (φ a1))=1 := by
  apply le_antisymm (max_le (hφ a0) (hφ a1))
  rcases hu with h0|h1
  · rw [←unit_norm φ v hφ a0 h0]
    exact le_max_left _ _
  · rw [←unit_norm φ v hφ a1 h1]
    exact le_max_right _ _

include hφ in
/-- A common change from the integral frame to a rational frame has exactly
its own norm as the pair maximum. This retains the actual frame scalar. -/
theorem scaled_pair_max (a0 a1 : A) (hu : IsUnit a0 ∨ IsUnit a1) (α : K) :
    max (v (α*φ a0)) (v (α*φ a1))=v α := by
  rw [map_mul,map_mul,←mul_max_of_nonneg _ _ (v.nonneg α),pair_max φ v hφ a0 a1 hu,mul_one]

include hφ in
/-- The normalized finite-place bound uses precisely the inverse norm of
the same frame scalar. No all-place metric or support condition is asserted. -/
theorem normalized_pair_bound (a0 a1 : A) (hu : IsUnit a0 ∨ IsUnit a1)
    (α : K) (hα : α≠0) :
    v (α*φ a0)*(v α)⁻¹≤1 ∧ v (α*φ a1)*(v α)⁻¹≤1 := by
  have hmax := scaled_pair_max φ v hφ a0 a1 hu α
  have h0 : v (α*φ a0)≤v α := (le_max_left _ _).trans_eq hmax
  have h1 : v (α*φ a1)≤v α := (le_max_right _ _).trans_eq hmax
  have hp : 0<v α := v.pos hα
  constructor
  · rw [←div_eq_mul_inv]
    exact (div_le_one hp).mpr h0
  · rw [←div_eq_mul_inv]
    exact (div_le_one hp).mpr h1
end IntegralUnitPairNorm318
