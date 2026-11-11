module
public import SplitKernelBaseChange318
public section
noncomputable section
namespace KernelComparisonTransport318
universe u v w z t
variable {R : Type u} [CommRing R]
  {A : Type v} [AddCommGroup A] [Module R A] {B : Type w} [AddCommGroup B] [Module R B]
  {A' : Type z} [AddCommGroup A'] [Module R A'] {B' : Type t} [AddCommGroup B'] [Module R B']
  (d : A →ₗ[R] B) (d' : A' →ₗ[R] B') (e : A ≃ₗ[R] A') (b : B ≃ₗ[R] B')
  (h : d'.comp e.toLinearMap = b.toLinearMap.comp d)

include h in
lemma forward_zero (x : LinearMap.ker d) : d' (e x) = 0 := by
  have hx := LinearMap.congr_fun h x
  change d' (e x) = b (d x) at hx
  rw [x.property,map_zero] at hx
  exact hx

include h in
lemma backward_zero (x : LinearMap.ker d') : d (e.symm x) = 0 := by
  apply b.injective
  have hx := LinearMap.congr_fun h (e.symm x)
  change d' (e (e.symm x)) = b (d (e.symm x)) at hx
  rw [LinearEquiv.apply_symm_apply,x.property] at hx
  exact hx.symm.trans (map_zero b).symm

/-- Kernel identification retains the specified genuine coefficient
comparison maps; no rank/dimension or arbitrary basis replacement. -/
@[expose] def equivalence : LinearMap.ker d ≃ₗ[R] LinearMap.ker d' where
  toFun x := ⟨e x,forward_zero d d' e b h x⟩
  invFun x := ⟨e.symm x,backward_zero d d' e b h x⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x
  right_inv x := by apply Subtype.ext; exact e.apply_symm_apply x
  map_add' x y := by apply Subtype.ext; exact e.map_add x y
  map_smul' r x := by apply Subtype.ext; exact e.map_smul r x
end KernelComparisonTransport318
