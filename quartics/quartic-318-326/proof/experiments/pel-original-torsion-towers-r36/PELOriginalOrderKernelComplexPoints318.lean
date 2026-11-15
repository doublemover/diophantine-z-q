module
public import PELOriginalOrderKernelCardinality318
public import PELOriginalOrderAutomorphisms318
public section
noncomputable section
namespace PELOriginalOrderKernelComplexPoints318
open AlgebraicGeometry CategoryTheory PELPrincipalOrderCoordinates318
open PELOriginalOrderIntegralNorm318 PELOriginalOrderKernelLatticeQuotient318
open PELOriginalSchemePointGroup318 PELOriginalTorusPointAddEquiv318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
/-- The actual original torus kernel and the actual represented complex
point kernel agree through the already proved theta additive equivalence. -/
@[expose] def originalEquiv : TorusKernel τ a ≃
    PELOriginalOrderKernelScheme318.PointKernel τ hτ a (𝟙 (Spec (CommRingCat.of ℂ))) where
  toFun q := ⟨originalAddEquiv τ hτ q.val,by
    rw [PELOriginalOrderAutomorphisms318.original_equiv_action,q.property,map_zero]⟩
  invFun p := ⟨(originalAddEquiv τ hτ).symm p.val,by
    apply (originalAddEquiv τ hτ).injective
    rw [←PELOriginalOrderAutomorphisms318.original_equiv_action,
      AddEquiv.apply_symm_apply,map_zero]
    exact p.property⟩
  left_inv q := by apply Subtype.ext; exact (originalAddEquiv τ hτ).symm_apply_apply q.val
  right_inv p := by apply Subtype.ext; exact (originalAddEquiv τ hτ).apply_symm_apply p.val
@[expose] def kernelEquiv :
    PELOriginalOrderKernelScheme318.KernelPoint τ hτ a (𝟙 (Spec (CommRingCat.of ℂ))) ≃
      TorusKernel τ a :=
  (PELOriginalOrderKernelScheme318.equivalence τ hτ a (𝟙 _)).trans (originalEquiv τ hτ a).symm
/-- Exact count of ALL genuine Spec(C)-valued points of the WHOLE
original order-kernel scheme. Scheme length is a separate finite-etale
comparison and is not inferred from this count alone. -/
lemma cardinality (ha : norm a≠0) :
    Nat.card (PELOriginalOrderKernelScheme318.KernelPoint τ hτ a (𝟙 (Spec (CommRingCat.of ℂ))))=
      (norm a).natAbs^2 := by
  rw [Nat.card_congr (kernelEquiv τ hτ a)]
  exact PELOriginalOrderKernelCardinality318.torus_card τ hτ a ha
end PELOriginalOrderKernelComplexPoints318
