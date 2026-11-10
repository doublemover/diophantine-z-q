module
public import TwoChartFiniteRelations318
public section
noncomputable section
namespace TwoChartFiniteRelationPresentation318
universe u v w z
variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {M : Type w} [AddCommGroup M] [Module R M]
  {K : Type z} [AddCommGroup K] [Module R K]
  (f : E →ₗ[R] M) (P Q : Submodule R E)
  (k : K →ₗ[R] LinearMap.ker f) (J : Submodule R K)
  (hJ : ∀ x ∈ J, k x ∈ TwoChartFiniteRelations318.kernelBoundary f P Q)

/-- A FINITE original relation quotient may be smaller than the full
kernel-Cech boundary quotient. Only actual inclusion of its chart relations
and surjectivity onto the original overlap kernel are needed. -/
@[expose] def comparison : (K ⧸ J) →ₗ[R]
    ((LinearMap.ker f) ⧸ TwoChartFiniteRelations318.kernelBoundary f P Q) :=
  J.liftQ ((TwoChartFiniteRelations318.kernelBoundary f P Q).mkQ.comp k) (by
    intro x hx
    change (TwoChartFiniteRelations318.kernelBoundary f P Q).mkQ (k x) = 0
    rw [Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact hJ x hx)

lemma comparison_surjective (hk : Function.Surjective k) :
    Function.Surjective (comparison f P Q k J hJ) := by
  intro z
  obtain ⟨y,rfl⟩ := (TwoChartFiniteRelations318.kernelBoundary f P Q).mkQ_surjective z
  obtain ⟨x,rfl⟩ := hk y
  exact ⟨J.mkQ x,rfl⟩

/-- Actual finite relation generators suffice for a finitely presented
H1 quotient, without falsely identifying their images with the entire
chart-comap kernels or assuming exactness of tensor on the left. -/
theorem finitePresentation (hf : Function.Surjective f) (hk : Function.Surjective k)
    [Module.FinitePresentation R (E ⧸ (P ⊔ Q))] [Module.Finite R (K ⧸ J)] :
    Module.FinitePresentation R (M ⧸ (P.map f ⊔ Q.map f)) := by
  letI : Module.Finite R ((LinearMap.ker f) ⧸ TwoChartFiniteRelations318.kernelBoundary f P Q) :=
    Module.Finite.of_surjective (comparison f P Q k J hJ)
      (comparison_surjective f P Q k J hJ hk)
  exact TwoChartFiniteRelations318.finitePresentation f P Q hf
end TwoChartFiniteRelationPresentation318
