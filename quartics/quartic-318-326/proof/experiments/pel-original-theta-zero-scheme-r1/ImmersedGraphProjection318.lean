module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public section
noncomputable section
namespace ImmersedGraphProjection318
open Filter Topology
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A genuine local reconstruction of an immersed map from a specified
projection forces the derivative of THAT projection to be injective.
This is used only after actual primitive-root reconstruction is supplied. -/
theorem projection_derivative_injective (f : E → F) (p : E → E) (g : E → F) (x : E)
    (hf : DifferentiableAt ℂ f x) (hp : DifferentiableAt ℂ p x)
    (hg : DifferentiableAt ℂ g (p x))
    (he : f =ᶠ[𝓝 x] fun y => g (p y))
    (hi : Function.Injective (fderiv ℂ f x)) :
    Function.Injective (fderiv ℂ p x) := by
  have hd : fderiv ℂ f x = (fderiv ℂ g (p x)).comp (fderiv ℂ p x) :=
    ((hg.hasFDerivAt.comp x hp.hasFDerivAt).congr_of_eventuallyEq he).fderiv
  intro v w hvw
  apply hi
  rw [hd]
  exact congrArg (fderiv ℂ g (p x)) hvw

/-- In equal finite dimension the SAME projection has a genuine local
inverse; no derivative-normalizing replacement projection is chosen. -/
theorem exists_projection_chart (f : E → F) (p : E → E) (g : E → F) (x : E)
    (hf : DifferentiableAt ℂ f x) (hp : ContDiffAt ℂ 1 p x)
    (hg : DifferentiableAt ℂ g (p x))
    (he : f =ᶠ[𝓝 x] fun y => g (p y))
    (hi : Function.Injective (fderiv ℂ f x)) :
    ∃ e : OpenPartialHomeomorph E E,
      x ∈ e.source ∧ (∀ y, e y = p y) ∧ ContDiffAt ℂ 1 e.symm (p x) := by
  have hpd : DifferentiableAt ℂ p x := hp.differentiableAt (by norm_num)
  have hinj := projection_derivative_injective f p g x hf hpd hg he hi
  let A : E ≃L[ℂ] E :=
    ((fderiv ℂ p x).toLinearMap.linearEquivOfInjective hinj rfl).toContinuousLinearEquiv
  have hA : (A : E →L[ℂ] E) = fderiv ℂ p x := by
    ext v
    rfl
  have hder : HasFDerivAt p (A : E →L[ℂ] E) x := hA.symm ▸ hpd.hasFDerivAt
  let e := hp.toOpenPartialHomeomorph p hder (by norm_num)
  exact ⟨e,hp.mem_toOpenPartialHomeomorph_source hder (by norm_num),
    fun _ => rfl,hp.to_localInverse hder (by norm_num)⟩
end ImmersedGraphProjection318
