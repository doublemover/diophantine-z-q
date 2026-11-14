module
public import ActualOriginalIndexedPrimitiveSource318
public import Mathlib.Data.Finset.Image
public section
noncomputable section
namespace ActualOriginalBoundedPrimitiveBox318
open QuadricCRTAssembly318 ActualOriginalCanonicalSupportBox318
open ActualOriginalPositiveRayScaling318 ActualOriginalPrimitiveRegionRays318

/-- Actual globally primitive original zeros in the entire centered box
and original positive region. No primality of form values is imposed. -/
@[expose] def primitiveBox {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ) (H : ℕ) :
    Finset (Quadric κ) := by
  classical
  exact ((centeredBox (H : ℤ)).subtype (fun z => equation κ z=0)).filter
    (fun u => u∈goodPrimitivePoints κ γ)

lemma actual_mem_primitive_box {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (H : ℕ) (u : Quadric κ) :
    u∈primitiveBox κ γ H ↔ u.1∈centeredBox (H : ℤ) ∧ u∈goodPrimitivePoints κ γ := by
  classical
  simp only [primitiveBox,Finset.mem_filter,Finset.mem_subtype]

lemma actual_integer_interval_shrink (H : ℤ) (d : ℕ) (hd : 0<d) (z : ℤ)
    (hz : (d : ℤ)*z∈Finset.Icc (-H) H) : z∈Finset.Icc (-H) H := by
  have hd1 : (1 : ℤ)≤d := by exact_mod_cast (show 1≤d by omega)
  have habs := abs_le.mpr (Finset.mem_Icc.mp hz)
  rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg d)] at habs
  have hh := mul_le_mul_of_nonneg_right hd1 (abs_nonneg z)
  exact Finset.mem_Icc.mpr (abs_le.mp (by nlinarith))

/-- Dividing by a positive integer moves ALL five coordinates into the
same centered box. This supplies bounded primitive representatives. -/
lemma actual_centered_box_shrink (H d : ℕ) (hd : 0<d) (u : Coordinates ℤ)
    (hu : scaleCoordinates (d : ℤ) u∈centeredBox (H : ℤ)) :
    u∈centeredBox (H : ℤ) := by
  have hh := Finset.mem_product.mp hu
  have hab := Finset.mem_product.mp hh.1
  have hcdw := Finset.mem_product.mp hh.2
  have hcd := Finset.mem_product.mp hcdw.1
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨actual_integer_interval_shrink _ d hd _ hab.1,actual_integer_interval_shrink _ d hd _ hab.2⟩,
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨actual_integer_interval_shrink _ d hd _ hcd.1,actual_integer_interval_shrink _ d hd _ hcd.2⟩,
      actual_integer_interval_shrink _ d hd _ hcdw.2⟩⟩
end ActualOriginalBoundedPrimitiveBox318
