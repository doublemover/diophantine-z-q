module

public import SelectedActualAbelNearbyMatrixSpectrum318
public import SelectedActualAbelFiberCharacterSpectrum318
public import SelectedActualAbelFiberMultiplicationBaseChange318
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Polynomial.AlgebraMap

public section

noncomputable section

open Filter Polynomial
open scoped Topology TensorProduct

namespace SelectedActualAbelNearbyFiberCharacters318

open SelectedActualAbelFiberMultiplicationBaseChange318
open SelectedActualAbelFiberCharacterSpectrum318
open SelectedActualAbelNearbyMatrixSpectrum318

variable {B : Type*} [CommRing B] [Algebra ℂ[X] B] [Algebra ℂ B]

private theorem fiber_polynomial_scalar (z : ℂ) (p : ℂ[X]) :
    intoFiber (B := B) z (algebraMap ℂ[X] B p) =
      algebraMap ℂ (Fiber (B := B) z) (p.eval z) := by
  letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
  have e₁ : algebraMap ℂ[X] (Fiber (B := B) z) p = (p.eval z) ⊗ₜ[ℂ[X]] (1 : B) :=
    Algebra.TensorProduct.algebraMap_apply p
  have e₂ : algebraMap ℂ (Fiber (B := B) z) (p.eval z) = (p.eval z) ⊗ₜ[ℂ[X]] (1 : B) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  exact ((intoFiber (B := B) z).commutes p).trans (e₁.trans e₂.symm)

variable [hTower : IsScalarTower ℂ ℂ[X] B]
include hTower

/-- Every character of the exact tensor fibre is a complex character
of the original ring over the prescribed value of its literal J. -/
def fromFiber (z : ℂ) (ψ : Fiber (B := B) z →ₐ[ℂ] ℂ) : B →ₐ[ℂ] ℂ where
  toRingHom := ψ.toRingHom.comp (intoFiber (B := B) z).toRingHom
  commutes' u := by
    change ψ (intoFiber (B := B) z (algebraMap ℂ B u)) = _
    rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] B, fiber_polynomial_scalar, ψ.commutes]
    have hc : algebraMap ℂ ℂ[X] u = Polynomial.C u := rfl
    rw [hc, Polynomial.eval_C]

theorem fromFiber_value (z : ℂ) (ψ : Fiber (B := B) z →ₐ[ℂ] ℂ) (b : B) :
    fromFiber z ψ b = ψ (intoFiber z b) := by rfl

theorem fromFiber_J (z : ℂ) (ψ : Fiber (B := B) z →ₐ[ℂ] ℂ) :
    fromFiber z ψ (algebraMap ℂ[X] B Polynomial.X) = z := by
  rw [fromFiber_value, fiber_polynomial_scalar, ψ.commutes,
    Polynomial.eval_X, Algebra.algebraMap_self_apply]

/-- A given original character over the coordinate z factors through
the entire specialized tensor algebra, with its exact given values. -/
theorem exists_fiber_character_of_value (z : ℂ) (f : B →ₐ[ℂ] ℂ)
    (hJ : f (algebraMap ℂ[X] B Polynomial.X) = z) :
    ∃ ψ : Fiber (B := B) z →ₐ[ℂ] ℂ, ∀ b : B, ψ (intoFiber z b) = f b := by
  letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
  letI : IsScalarTower ℂ[X] ℂ ℂ := IsScalarTower.of_algebraMap_eq
    (fun a => (Algebra.algebraMap_self_apply (algebraMap ℂ[X] ℂ a)).symm)
  have he : f.comp (IsScalarTower.toAlgHom ℂ ℂ[X] B) = Polynomial.aeval z := by
    apply Polynomial.algHom_ext
    change f (algebraMap ℂ[X] B Polynomial.X) = Polynomial.aeval z Polynomial.X
    rw [Polynomial.aeval_X]
    exact hJ
  let g : B →ₐ[ℂ[X]] ℂ := {
    toRingHom := f.toRingHom
    commutes' a := by
      have h := congrArg (fun p : ℂ[X] →ₐ[ℂ] ℂ => p a) he
      change f (algebraMap ℂ[X] B a) = Polynomial.aeval z a at h
      change f (algebraMap ℂ[X] B a) = a.eval z
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using h }
  let ψ : Fiber (B := B) z →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) g (fun x y => Commute.all _ _)
  refine ⟨ψ, fun b => ?_⟩
  change ψ ((1 : ℂ) ⊗ₜ[ℂ[X]] b) = f b
  unfold ψ
  rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, one_mul] <;> rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem spectral_value_at_actual_character
    (basis : Module.Basis ι ℂ[X] B) (b : B) (z : ℂ)
    (f : B →ₐ[ℂ] ℂ) (hJ : f (algebraMap ℂ[X] B Polynomial.X) = z) :
    (Matrix.scalar ι (f b) - (Algebra.leftMulMatrix basis b).map (evalRingHom z)).det = 0 := by
  letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
  obtain ⟨ψ,hψ⟩ := exists_fiber_character_of_value z f hJ
  rw [← actual_fiber_leftMulMatrix basis b z]
  exact (determinant_zero_iff_character (basis.baseChange ℂ) (intoFiber z b) (f b)).2
    ⟨ψ,hψ b⟩

private theorem actual_character_of_spectral_value
    (basis : Module.Basis ι ℂ[X] B) (b : B) (z u : ℂ)
    (h : (Matrix.scalar ι u - (Algebra.leftMulMatrix basis b).map (evalRingHom z)).det = 0) :
    ∃ f : B →ₐ[ℂ] ℂ, f (algebraMap ℂ[X] B Polynomial.X) = z ∧ f b = u := by
  letI : Algebra ℂ[X] ℂ := evaluationAlgebra z
  rw [← actual_fiber_leftMulMatrix basis b z] at h
  obtain ⟨ψ,hψ⟩ := (determinant_zero_iff_character (basis.baseChange ℂ) (intoFiber z b) u).1 h
  exact ⟨fromFiber z ψ, fromFiber_J z ψ, (fromFiber_value z ψ b).trans hψ⟩

/-- At an actual character over the limiting J-value, a nearby
specialization has an actual character with nearby value on the chosen
element b. This does not assume reducedness or choose a branch.
In the density proof b is the CRT element separating the prescribed
point from all other points in that same fibre. -/
theorem eventually_near_character_on_element
    (basis : Module.Basis ι ℂ[X] B) (b : B) (z₀ : ℂ)
    (f₀ : B →ₐ[ℂ] ℂ) (hJ : f₀ (algebraMap ℂ[X] B Polynomial.X) = z₀)
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ z in 𝓝 z₀, ∃ f : B →ₐ[ℂ] ℂ,
      f (algebraMap ℂ[X] B Polynomial.X) = z ∧ ‖f₀ b - f b‖ < r := by
  refine (eventually_det_zero_near ι (Algebra.leftMulMatrix basis b) z₀ (f₀ b)
    (spectral_value_at_actual_character basis b z₀ f₀ hJ) r hr).mono ?_
  intro z hz
  obtain ⟨u,hu,hnear⟩ := hz
  obtain ⟨f,hfJ,hf⟩ := actual_character_of_spectral_value basis b z u hu
  exact ⟨f,hfJ,hf.symm ▸ hnear⟩

end SelectedActualAbelNearbyFiberCharacters318

#print axioms SelectedActualAbelNearbyFiberCharacters318.exists_fiber_character_of_value
#print axioms SelectedActualAbelNearbyFiberCharacters318.eventually_near_character_on_element
