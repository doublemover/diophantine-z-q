module
public import ActualOriginalBoundedPrimitiveBox318
public section
noncomputable section
namespace ActualOriginalBoundedPrimitiveCover318
open QuadricCRTAssembly318 ActualOriginalBoundedPrimitiveBox318
open ActualOriginalFinitePrimitiveRayCover318 ActualOriginalPrimitiveRegionRays318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCompactCircleCount318 ActualOriginalRealGoodRegion318

/-- Every actually weighted original zero is covered by the primitive
points in the SAME radius box, not by a hypothetical global finite set. -/
theorem actual_bounded_primitive_cover {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (W : Coordinates ℝ → ℝ) (hW : ∀ y∈tsupport W,y∈region γ)
    (B : ℝ) (hB : 0<B) (H : ℕ)
    (hsupport : ∀ z∉centeredBox (H : ℤ), latticeWeight B W z=0)
    (v : Coordinates ℤ) (hv : equation κ v=0) (hw : latticeWeight B W v≠0) :
    v∈rayBox κ (primitiveBox κ γ H) H := by
  classical
  let z : Quadric κ := ⟨v,hv⟩
  have hreg := actual_weight_nonzero_region γ W hW B hB v hw
  obtain ⟨d,hd,u,hu,he⟩ := actual_good_primitive_factor κ γ z hreg
  have hzbox : z.1∈centeredBox (H : ℤ) := by
    by_contra hh
    exact hw (hsupport v hh)
  have hubox : u.1∈centeredBox (H : ℤ) :=
    actual_centered_box_shrink H d hd u.1 (he ▸ hzbox)
  have humem := (actual_mem_primitive_box κ γ H u).mpr ⟨hubox,hu⟩
  have hua : (0 : ℝ)<(u.1.1.1 : ℝ) := hu.2.1
  have hdH := actual_ray_multiplier_bound κ H d z u hzbox (by exact_mod_cast hua) he
  exact Finset.mem_image.mpr ⟨(u,d),Finset.mem_product.mpr ⟨humem,
    Finset.mem_range.mpr (by omega)⟩,he.symm⟩
end ActualOriginalBoundedPrimitiveCover318
