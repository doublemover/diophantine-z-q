module
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public section
namespace FlatCokernelDiagram318
universe u
variable {R : Type u} [CommRing R]
variable {A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ : Type u}
  [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
  [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
  [AddCommGroup C₀] [AddCommGroup C₁]
  [Module R A₀] [Module R A₁] [Module R A₂]
  [Module R B₀] [Module R B₁] [Module R B₂]
  [Module R C₀] [Module R C₁]

/-- The explicit diagram chase for flat cokernels. The bottom injection
is essential: injectivity of the first two vertical arrows alone does
not make their cokernel map injective. -/
lemma injective_cokernel_map
    (f₀ : A₀ →ₗ[R] B₀) (f₁ : A₁ →ₗ[R] B₁) (f₂ : A₂ →ₗ[R] B₂)
    (q₀ : B₀ →ₗ[R] C₀) (q₁ : B₁ →ₗ[R] C₁)
    (a : A₀ →ₗ[R] A₁) (a' : A₁ →ₗ[R] A₂)
    (b : B₀ →ₗ[R] B₁) (b' : B₁ →ₗ[R] B₂) (c : C₀ →ₗ[R] C₁)
    (hq₀ : Function.Surjective q₀)
    (hrow : Function.Exact f₁ q₁) (hcol : Function.Exact a a')
    (hqf : q₀.comp f₀ = 0) (hbb : b'.comp b = 0)
    (hleft : b.comp f₀ = f₁.comp a)
    (hright : c.comp q₀ = q₁.comp b)
    (hbottom : b'.comp f₁ = f₂.comp a')
    (hb : Function.Injective b) (hf₂ : Function.Injective f₂) :
    Function.Injective c := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have hx0 : c x = 0 := hx
  obtain ⟨y, rfl⟩ := hq₀ x
  have hby : b y ∈ LinearMap.ker q₁ := by
    change q₁ (b y) = 0
    rw [← LinearMap.comp_apply, ← hright, LinearMap.comp_apply]
    exact hx0
  rw [LinearMap.exact_iff.mp hrow] at hby
  obtain ⟨z, hz⟩ := hby
  have haz : a' z = 0 := by
    apply hf₂
    rw [map_zero, ← LinearMap.comp_apply, ← hbottom,
      LinearMap.comp_apply, hz, ← LinearMap.comp_apply, hbb]
    rfl
  have hzrange : z ∈ LinearMap.ker a' := haz
  rw [LinearMap.exact_iff.mp hcol] at hzrange
  obtain ⟨w, hw⟩ := hzrange
  have hy : y = f₀ w := hb (by
    rw [← hz, ← hw, ← LinearMap.comp_apply, ← hleft,
      LinearMap.comp_apply])
  rw [hy, ← LinearMap.comp_apply, hqf]
  rfl
end FlatCokernelDiagram318
