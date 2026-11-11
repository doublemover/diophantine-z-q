module
public import FourRootActualOrderAutomorphisms318
public section
noncomputable section
namespace FourRootFullFiniteInertia318
open FourRootActualGenericField318 FourRootAffineTensorPresentation318
open FourRootActualFractionField318 FourRootActualResidueInertia318
open FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra

lemma polynomial_inertia_iff (g:FourBinaryCharacters318.Group) (p:FinitePoints b):
    FourRootActualOrderAutomorphisms318.polynomialSign b g∈
      (finitePrime b p).inertia (A b≃ₐ[P]A b) ↔
    FourRootCoordinateRingSigns318.finiteEquiv b g∈
      (finitePrime b p).inertia (A b≃ₐ[ℂ]A b):=by
  simp only [Ideal.mem_inertia]
  change (∀x,FourRootActualOrderAutomorphisms318.polynomialSign b g x-x∈finitePrime b p) ↔ _
  simp only [FourRootActualOrderAutomorphisms318.polynomialSign_apply]

/-- The FULL actual polynomial-order inertia subgroup, not merely the
subgroup of already-known labels, has the two original branch signs. -/
@[expose] def branchInertiaEquivalence (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    (finitePrime b p).inertia (A b≃ₐ[P]A b)≃Bool:=
  ((FourRootActualOrderAutomorphisms318.signEquivalence b hb).subtypeEquiv
    (fun g=>(polynomial_inertia_iff b g p).symm)).symm.trans
      (FourRootInertiaLabelCardinality318.finiteEquivalence b hb j p hp)

theorem full_inertia_card (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    Nat.card ((finitePrime b p).inertia (A b≃ₐ[P]A b))=2:=by
  rw [Nat.card_congr (branchInertiaEquivalence b hb j p hp)]
  simp

/-- Any full actual inertia automorphism has a UNIQUE original sign
label supported on the one ramified root. This still does not substitute
an inertia count for the separately required ramification-index theorem. -/
theorem inertia_original_label (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j)
    (e:A b≃ₐ[P]A b) (he:e∈(finitePrime b p).inertia (A b≃ₐ[P]A b)):
    ∃!g:FourBinaryCharacters318.Group,
      FourRootActualOrderAutomorphisms318.polynomialSign b g=e∧
        ∀k,k≠j→FourBinaryCharacters318.coordinate (F:=ℂ) k g=1:=by
  obtain ⟨g,rfl⟩:=FourRootActualOrderAutomorphisms318.sign_surjective b hb e
  have hg:∀k,k≠j→FourBinaryCharacters318.coordinate (F:=ℂ) k g=1:=
    (finite_branch_inertia b hb g j p hp).mp ((polynomial_inertia_iff b g p).mp he)
  refine ⟨g,⟨rfl,hg⟩,?_⟩
  intro h hh
  exact FourRootActualOrderAutomorphisms318.sign_injective b hb hh.1
end FourRootFullFiniteInertia318
