module
public import PELOriginalTorsionEnumeration318
public section
noncomputable section
namespace PELOriginalKernelComplexCardinality318
open AlgebraicGeometry CategoryTheory PELComplexPeriodSurface318
open PELOriginalTorsionKernelScheme318 PELOriginalTorsionPointComparison318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ) (hn : 0<n)
@[expose] def integerTorsionEquiv : {q : Surface τ // n • q=0} ≃
    {q : Surface τ // (n : ℤ) • q=0} where
  toFun q := ⟨q.val,by simpa only [natCast_zsmul] using q.property⟩
  invFun q := ⟨q.val,by simpa only [natCast_zsmul] using q.property⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

/-- Exact original integral lattice representatives identify ALL
complex scheme points of the ACTUAL scheme-theoretic multiplication
kernel, with both inverse maps, preserving their original point action. -/
@[expose] def enumeration : (Fin 4 → Fin n) ≃
    KernelPoints τ hτ (n : ℤ) (Spec (CommRingCat.of ℂ)) (𝟙 _) :=
  (PELOriginalTorsionEnumeration318.equivalence τ hτ n hn).trans
    ((integerTorsionEquiv τ n).trans (kernelOriginalEquiv τ hτ (n : ℤ)).symm)
include hn in
lemma finite : Finite (KernelPoints τ hτ (n : ℤ) (Spec (CommRingCat.of ℂ)) (𝟙 _)) :=
  Finite.of_equiv (Fin 4 → Fin n) (enumeration τ hτ n hn)
include hn in
lemma cardinality :
    Nat.card (KernelPoints τ hτ (n : ℤ) (Spec (CommRingCat.of ℂ)) (𝟙 _))=n^4 := by
  rw [←Nat.card_congr (enumeration τ hτ n hn)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin]
lemma original_point (a : Fin 4 → Fin n) :
    (enumeration τ hτ n hn a).val≫inclusion τ hτ (n : ℤ)=
      PELOriginalCandidateComplexPoints318.candidateComplexPoint τ hτ
        (DiscreteComplexPeriodAtlas318.projection (Periods τ)
          (PELOriginalTorsionRepresentatives318.vector τ hτ n a)) := by
  rw [kernelOriginal_point]
  change PELOriginalCandidateComplexPoints318.candidateComplexPoint τ hτ
    ((kernelOriginalEquiv τ hτ (n : ℤ))
      ((kernelOriginalEquiv τ hτ (n : ℤ)).symm _)).val=_
  rw [Equiv.apply_symm_apply]
  rfl
end PELOriginalKernelComplexCardinality318
