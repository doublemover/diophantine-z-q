module
public import IntegralOtherRootCoordinates318
public import IntegralRationalInfinityCoordinate318
public import IntegralInfinityOriginalField318
public import InfinityOrderCoordinates318
public section
noncomputable section
namespace IntegralRationalInfinityMap318
open Polynomial
open IntegralOverlapChartMaps318 IntegralInfinityCommonBase318 IntegralOverlapRootGenerators318
open IntegralRationalFullOverlap318 IntegralOriginalRootCoordinates318 IntegralInfinityOriginalField318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
/-- Normalize scalar multiplication before installing the concrete overlap
algebras. The scalar map is the given algebra map, not a new action. -/
private theorem mapped_smul {S A B : Type*} [CommRing S] [CommRing A]
    [CommRing B] [Algebra S A] (f : A →+* B) (r : S) (a : A) :
    f (r • a) = f (algebraMap S A r) * f a := by
  rw [Algebra.smul_def, map_mul]

/-- The rational constants agree for any two ring maps. Keeping this fact
on abstract carriers avoids unfolding the entire original Kummer field. -/
private theorem rational_polynomial_ext {T : Type*} [CommRing T]
    (f g : ℚ[X] →+* T) (hX : f X = g X) : f = g := by
  apply Polynomial.ringHom_ext
  · intro q
    exact RingHom.congr_fun (RingHom.ext_rat (f.comp C) (g.comp C)) q
  · exact hX

private theorem localized_polynomial_ext {A T : Type*} [CommRing A]
    [CommRing T] [Algebra ℚ[X] A] (d : ℚ[X]) [IsLocalization.Away d A]
    (f g : A →+* T)
    (hX : f (algebraMap ℚ[X] A X) = g (algebraMap ℚ[X] A X)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers d)
  exact rational_polynomial_ext _ _ hX

/-- Check the full localized polynomial base and all three ordered roots
before specializing the nested original chart and field carriers. -/
private theorem rational_order_ext (a : Fin 3 → ℚ[X]) {T : Type*} [CommRing T]
    (f g : Presentation a →+* T)
    (hX : f (algebraMap (Localization.Away (∏ k : Fin 3, a k)) (Presentation a)
        (algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3, a k)) X)) =
      g (algebraMap (Localization.Away (∏ k : Fin 3, a k)) (Presentation a)
        (algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3, a k)) X)))
    (hroot : ∀ j, f (ThreeRootCoordinates318.generator
        (fun i => algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3, a k)) (a i)) j) =
      g (ThreeRootCoordinates318.generator
        (fun i => algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3, a k)) (a i)) j)) :
    f = g := by
  apply ThreeRootCoordinates318.ringHom_ext
  · apply localized_polynomial_ext (∏ k : Fin 3, a k)
    exact hX
  · exact hroot

variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (InfinityFieldCoordinates318.L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- Restrict the three actual integral infinity generators into the SAME
original field. Each is the original ordered quotient y_j/y0 with its sign. -/
theorem generator_original_field (j : Fin 3) :
    originalFieldEmbedding c (infinityMap ℚ c (infinityGenerator ℚ c j)) =
      InfinityFieldCoordinates318.ratio c j := by
  rw [infinityMap_generator]
  refine (mapped_smul (S := CommonBase ℚ c) (A := Overlap ℚ c)
    (originalFieldEmbedding c) (↑(rootUnit ℚ c)⁻¹ : CommonBase ℚ c)
    (1 ⊗ₜ[IntegralSourceBranches318.OpenBase ℚ c 0] finiteGenerator ℚ c j)).trans ?_
  have hunit : originalFieldEmbedding c
      (commonMap ℚ c (↑(rootUnit ℚ c)⁻¹ : CommonBase ℚ c)) =
        (InfinityFieldCoordinates318.root c 0)⁻¹ := by
    have h := congrArg ((originalFieldEmbedding c).comp (commonMap ℚ c).toRingHom)
      (Units.mul_inv (rootUnit ℚ c))
    simp only [RingHom.comp_apply,map_mul,map_one] at h
    -- Expose the algebra-hom applications before matching the signed-root theorem.
    change originalFieldEmbedding c (commonMap ℚ c (rootUnit ℚ c : CommonBase ℚ c)) *
      originalFieldEmbedding c (commonMap ℚ c (↑(rootUnit ℚ c)⁻¹ : CommonBase ℚ c)) = 1 at h
    rw [IntegralRationalInfinityCoordinate318.root_zero] at h
    exact eq_inv_of_mul_eq_one_right h
  change originalFieldEmbedding c (commonMap ℚ c (↑(rootUnit ℚ c)⁻¹ : CommonBase ℚ c)) *
    originalFieldEmbedding c (1 ⊗ₜ[IntegralSourceBranches318.OpenBase ℚ c 0]
      finiteGenerator ℚ c j) = _
  rw [hunit,IntegralOtherRootCoordinates318.common_other,originalFieldEmbedding_source,
    rational_root,ContactRootReciprocals318.embedding_root]
  exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm

theorem presentationEquiv_generator {a b : Fin 3 → ℚ[X]} (h : a=b) (j : Fin 3) :
    presentationEquiv h (ThreeRootCoordinates318.generator
      (fun i => algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3,a k)) (a i)) j) =
      ThreeRootCoordinates318.generator
        (fun i => algebraMap ℚ[X] (Localization.Away (∏ k : Fin 3,b k)) (b i)) j := by
  subst b
  rfl

theorem rationalOrderEquiv_generator (j : Fin 3) :
    rationalOrderEquiv c (infinityGenerator ℚ c j) = InfinityOrderCoordinates318.generator c j :=
  presentationEquiv_generator (funext (IntegralInfinityCoefficients318.rational_coefficient c)) j

/-- Equality of the actual full infinity-order field embeddings, checked on
its entire localized polynomial base and all THREE presentation generators. -/
theorem field_restriction :
    (originalFieldEmbedding c).comp (infinityMap ℚ c).toRingHom = originalEmbedding c := by
  apply rational_order_ext (fun j => IntegralInfinityChart318.coefficient ℚ c j)
  · have hX := (IntegralRationalInfinityCoordinate318.reciprocal_coordinate c).trans
      (original_coordinate c).symm
    rw [RingHom.comp_apply]
    change originalFieldEmbedding c (infinityMap ℚ c (IntegralInfinityChart318.coordinate ℚ c)) =
      originalEmbedding c (IntegralInfinityChart318.coordinate ℚ c)
    exact hX
  · intro j
    -- Unfold only this named composite, rather than asking defeq to reconstruct
    -- its nested field embedding while checking an expected transitivity goal.
    have hroot : originalEmbedding c (infinityGenerator ℚ c j) =
        InfinityFieldCoordinates318.ratio c j := by
      unfold originalEmbedding
      rw [RingHom.comp_apply]
      change InfinityOpenFractionField318.openEmbedding c
        (rationalOrderEquiv c (infinityGenerator ℚ c j)) = _
      rw [rationalOrderEquiv_generator, InfinityOrderCoordinates318.generator_embedding]
    have h := (generator_original_field c j).trans hroot.symm
    rw [RingHom.comp_apply]
    change originalFieldEmbedding c (infinityMap ℚ c (infinityGenerator ℚ c j)) =
      originalEmbedding c (infinityGenerator ℚ c j)
    exact h

/-- The full infinity restriction commutes with the original rational atlas.
The proof uses all generators and injectivity of the ORIGINAL open embedding. -/
theorem infinity_restriction (a : IntegralInfinityChart318.Order ℚ c) :
    overlapEquiv c (infinityMap ℚ c a) =
      InfinityOverlapLocalization318.toOpen c (rationalOrderEquiv c a) := by
  apply SourceOpenFractionField318.openEmbedding_injective c
  have he := RingHom.congr_fun (field_restriction c) a
  exact he.trans (InfinityOverlapLocalization318.toOpen_embedding c (rationalOrderEquiv c a)).symm
end IntegralRationalInfinityMap318
