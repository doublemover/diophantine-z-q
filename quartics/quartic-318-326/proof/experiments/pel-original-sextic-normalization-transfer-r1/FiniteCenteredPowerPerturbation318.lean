module
public import FinitePolynomialPowerPerturbation318
public section
noncomputable section
namespace FiniteCenteredPowerPerturbation318
variable {ι K A : Type*} [Fintype ι] [DecidableEq ι]
  [Field K] [CommRing A] [Nontrivial A] [Algebra K A]

/-- Translating the old normalization coordinates preserves WHOLE
finiteness by an actual surjective polynomial substitution and its
explicit inverse, not merely equality of fraction fields. -/
theorem shifted_finite (b : ι → A)
    (hf : (MvPolynomial.aeval b : MvPolynomial ι K →ₐ[K] A).Finite) (c : ι → K) :
    (MvPolynomial.aeval (fun i => b i-algebraMap K A (c i)) :
      MvPolynomial ι K →ₐ[K] A).Finite := by
  let σ : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i-MvPolynomial.C (c i))
  let ρ : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i+MvPolynomial.C (c i))
  have hinv : σ.comp ρ = AlgHom.id K (MvPolynomial ι K) := by
    ext i
    simp [σ,ρ]
  have hsurj : Function.Surjective σ := by
    intro p
    exact ⟨ρ p,congrArg (fun f : MvPolynomial ι K →ₐ[K] MvPolynomial ι K => f p) hinv⟩
  have hsquare : (MvPolynomial.aeval b).comp σ =
      MvPolynomial.aeval (fun i => b i-algebraMap K A (c i)) := by
    ext i
    simp [σ]
  rw [←hsquare]
  exact hf.comp (AlgHom.Finite.of_surjective σ hsurj)

/-- The high powers vanish to order at least two at the SPECIFIED
original evaluation. The resulting finite normalization has the same
values there as the prescribed elements. -/
theorem exists_centered_perturbation (b l : ι → A)
    (hf : (MvPolynomial.aeval b : MvPolynomial ι K →ₐ[K] A).Finite)
    (v : A →ₐ[K] K) :
    ∃ M : ℕ, 2 ≤ M ∧
      (MvPolynomial.aeval (fun i => l i+(b i-algebraMap K A (v (b i)))^M) :
        MvPolynomial ι K →ₐ[K] A).Finite ∧
      ∀ i, v (l i+(b i-algebraMap K A (v (b i)))^M) = v (l i) := by
  obtain ⟨M,hM,hfinite⟩ := FinitePolynomialPowerPerturbation318.exists_finite_perturbation
    (fun i => b i-algebraMap K A (v (b i))) l (shifted_finite b hf (fun i => v (b i)))
  refine ⟨M,hM,hfinite,?_⟩
  intro i
  have hM0 : M ≠ 0 := by omega
  simp only [map_add,map_pow,map_sub,AlgHom.commutes,sub_self,zero_pow hM0,add_zero]
end FiniteCenteredPowerPerturbation318
