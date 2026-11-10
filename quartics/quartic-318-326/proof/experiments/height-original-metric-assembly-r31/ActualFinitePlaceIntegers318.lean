module
public import IntegralChartFrameBounds318
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public section
noncomputable section
namespace ActualFinitePlaceIntegers318
open NumberField
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type*} [Field K] [NumberField K] (v : FinitePlace K)

/-- The actual valuation integer ring of the maximal ideal defining the
finite place, inside the original point field. -/
abbrev Integers := (v.maximalIdeal.valuation K).integer
instance : IsDiscreteValuationRing (Integers v) := inferInstance

/-- The given number-field absolute value and its actual discrete valuation
have exactly the same unit ball, with the standard place normalization. -/
theorem bounded_iff (x : K) : v x≤1 ↔ v.maximalIdeal.valuation K x≤1 := by
  rw [←FinitePlace.norm_embedding_eq v x,FinitePlace.norm_embedding']
  exact_mod_cast WithZeroMulInt.toNNReal_le_one_iff
    (HeightOneSpectrum.one_lt_absNorm_nnreal v.maximalIdeal)

theorem integer_bound (a : Integers v) : v (algebraMap (Integers v) K a)≤1 :=
  (bounded_iff v _).mpr a.property

theorem center_bound {A : Type*} [CommRing A] (φ : A →+* Integers v) (a : A) :
    v (((algebraMap (Integers v) K).comp φ) a)≤1 := integer_bound v (φ a)

/-- A norm-one field element is a unit of THIS actual valuation ring. -/
@[expose] def unitOfNormOne (x : K) (hx : v x=1) : (Integers v)ˣ where
  val := ⟨x,(bounded_iff v x).mp hx.le⟩
  inv := ⟨x⁻¹,(bounded_iff v x⁻¹).mp (by simpa only [map_inv₀,hx,inv_one] using (le_rfl : (1:ℝ)≤1))⟩
  val_inv := by
    apply Subtype.ext
    exact mul_inv_cancel₀ (by intro h; simp only [h,map_zero] at hx; norm_num at hx)
  inv_val := by
    apply Subtype.ext
    exact inv_mul_cancel₀ (by intro h; simp only [h,map_zero] at hx; norm_num at hx)

@[simp] theorem unitOfNormOne_value (x : K) (hx : v x=1) :
    algebraMap (Integers v) K (unitOfNormOne v x hx:Integers v)=x := rfl
end ActualFinitePlaceIntegers318
