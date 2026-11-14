module
public import ActualOriginalPrimitiveRegionRays318
public section
noncomputable section
namespace ActualOriginalFinitePrimitiveRayCover318
open QuadricCRTAssembly318 ActualOriginalPositiveRayScaling318 ActualOriginalPrimitiveRegionRays318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCompactCircleCount318 ActualOriginalRealGoodRegion318
open ActualOriginalIntegerTiling318

/-- Overlap-safe finite covering of all positive integer multiples up
to H. No uniqueness of primitive representatives is presumed. -/
@[expose] def rayBox (κ : ℤ) (S : Finset (Quadric κ)) (H : ℕ) : Finset (Coordinates ℤ) := by
  classical
  exact (S.product (Finset.range (H+1))).image (fun ud => scaleCoordinates (ud.2 : ℤ) ud.1.1)

lemma actual_ray_box_card (κ : ℤ) (S : Finset (Quadric κ)) (H : ℕ) :
    (rayBox κ S H).card≤S.card*(H+1) := by
  classical
  apply (Finset.card_image_le).trans_eq
  simp only [Finset.card_product,Finset.card_range]

/-- Positivity of the primitive first coordinate bounds the multiplier
by the actual box radius, not a new or assumed height. -/
lemma actual_ray_multiplier_bound (κ : ℤ) (H d : ℕ) (v u : Quadric κ)
    (hv : v.1∈centeredBox (H : ℤ)) (hu : 0<u.1.1.1)
    (he : v.1=scaleCoordinates (d : ℤ) u.1) : d≤H := by
  have hh := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hv).1).1).2
  have he' : v.1.1.1=(d : ℤ)*u.1.1.1 := congrArg (fun x : Coordinates ℤ => x.1.1) he
  have hu1 : 1≤u.1.1.1 := by omega
  have hm := mul_le_mul_of_nonneg_left hu1 (Int.natCast_nonneg d)
  omega

/-- If S contains ALL good primitive points, every nonzero original
weighted zero in the same support box lies in its finite ray cover. -/
theorem actual_primitive_ray_support {J : Type*} [Fintype J] (κ : ℤ) (γ : J → ℝ)
    (S : Finset (Quadric κ)) (hS : ∀ u∈goodPrimitivePoints κ γ,u∈S)
    (W : Coordinates ℝ → ℝ) (hW : ∀ y∈tsupport W,y∈region γ)
    (B : ℝ) (hB : 0<B) (H : ℕ)
    (hsupport : ∀ z∉centeredBox (H : ℤ), latticeWeight B W z=0)
    (v : Coordinates ℤ) (hv : equation κ v=0) (hw : latticeWeight B W v≠0) :
    v∈rayBox κ S H := by
  classical
  let z : Quadric κ := ⟨v,hv⟩
  have hreg := actual_weight_nonzero_region γ W hW B hB v hw
  obtain ⟨d,hd,u,hu,he⟩ := actual_good_primitive_factor κ γ z hreg
  have hzbox : z.1∈centeredBox (H : ℤ) := by
    by_contra hh
    exact hw (hsupport v hh)
  have hua : (0 : ℝ)<(u.1.1.1 : ℝ) := hu.2.1
  have hdH := actual_ray_multiplier_bound κ H d z u hzbox (by exact_mod_cast hua) he
  exact Finset.mem_image.mpr ⟨(u,d),Finset.mem_product.mpr ⟨hS u hu,
    Finset.mem_range.mpr (by omega)⟩,he.symm⟩

end ActualOriginalFinitePrimitiveRayCover318
