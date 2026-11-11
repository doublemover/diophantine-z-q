module
public import PELOriginalCubicAdditionConstants318
public import PELOriginalAllLevelProjectiveMap318
public section
noncomputable section
namespace PELOriginalAdditionTensorMap318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCubicAdditionConstants318

/-- Literal finite Segre coordinates, without a selected source point. -/
@[expose] def segre {I J : Type*} (x : I → ℂ) (y : J → ℂ) : I × J → ℂ :=
  fun ij => x ij.1 * y ij.2

lemma segre_ne_zero {I J : Type*} (x : I → ℂ) (y : J → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) : segre x y ≠ 0 := by
  intro h
  apply hx
  funext i
  by_contra hi
  apply hy
  funext j
  have hzero := congrFun h (i,j)
  change x i * y j = 0 at hzero
  exact (mul_eq_zero.mp hzero).resolve_left hi

variable (τ : ℂ) (hτ : 0 < τ.im)

/-- One fixed linear map between the actual finite tensor-coordinate spaces.
It is defined on ALL vectors, not just the analytic theta image. -/
@[expose] def additionMap : ((Label 6 × Label 6) → ℂ) →ₗ[ℂ]
    ((Label 3 × Label 3) → ℂ) where
  toFun w i := ∑ u : Label 6, ∑ v : Label 6,
    additionConstant τ hτ i.1 i.2 u v * w (u,v)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    funext i
    simp only [RingHom.id_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    ring

/-- The SAME constant finite linear map sends the actual full level-six
Segre input to the literal cubic sum/difference Segre output. -/
theorem actual_tensor_image (z a : ComplexVectors) :
    additionMap τ hτ (segre (fun u => value τ hτ 6 u z)
      (fun v => value τ hτ 6 v a)) =
      segre (fun r => value τ hτ 3 r (z+a))
        (fun s => value τ hτ 3 s (z-a)) := by
  funext i
  simpa only [additionMap,LinearMap.coe_mk,AddHom.coe_mk,segre,mul_assoc] using
    (actual_addition_formula τ hτ i.1 i.2 z a).symm

/-- There are no base points on ANY genuine original input pair, including
all former finite/projection/generator denominator boundaries. -/
theorem actual_image_ne_zero (z a : ComplexVectors) :
    additionMap τ hτ (segre (fun u => value τ hτ 6 u z)
      (fun v => value τ hτ 6 v a)) ≠ 0 := by
  rw [actual_tensor_image]
  exact segre_ne_zero _ _
    (PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 1 (z+a))
    (PELOriginalAllLevelProjectiveMap318.coverVector_nonzero τ hτ 1 (z-a))

/-- Every rank-one relation holds on the actual output tensor, with its
original sum and difference factors identified, not merely an existential
rank-one factorization. -/
theorem actual_rank_one (z a : ComplexVectors) (r r' s s' : Label 3) :
    let w := additionMap τ hτ (segre (fun u => value τ hτ 6 u z)
      (fun v => value τ hτ 6 v a))
    w (r,s) * w (r',s') = w (r,s') * w (r',s) := by
  dsimp only
  rw [actual_tensor_image]
  simp only [segre]
  ring
end PELOriginalAdditionTensorMap318
