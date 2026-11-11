module
public import PELOriginalTorsionKernelScheme318
public section
noncomputable section
namespace PELOriginalTorsionPointComparison318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalPolarizationTransitions318 PELOriginalSchemePointGroup318
open PELOriginalTorusPointAddEquiv318 PELOriginalTorsionKernelScheme318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)

/-- The ORIGINAL torus torsion condition, with the same integer and no
change of lattice, identifies the whole algebraic point subgroup. -/
lemma original_torsion_iff (q : Base τ) :
    n • originalAddEquiv τ hτ q=0 ↔ n • q=0 := by
  rw [←map_zsmul,←map_zero (originalAddEquiv τ hτ)]
  exact (originalAddEquiv τ hτ).injective.eq_iff

@[expose] def originalTorsionEquiv : {q : Base τ // n • q=0} ≃
    torsion τ hτ n (𝟙 (Spec (CommRingCat.of ℂ))) where
  toFun q := ⟨originalAddEquiv τ hτ q.val,(original_torsion_iff τ hτ n q.val).mpr q.property⟩
  invFun p := ⟨(originalAddEquiv τ hτ).symm p.val,by
    apply (original_torsion_iff τ hτ n _).mp
    simpa only [AddEquiv.apply_symm_apply] using p.property⟩
  left_inv q := by apply Subtype.ext; exact (originalAddEquiv τ hτ).symm_apply_apply q.val
  right_inv p := by apply Subtype.ext; exact (originalAddEquiv τ hτ).apply_symm_apply p.val

/-- Full complex-point comparison for the actual scheme-theoretic
kernel, with both inverse maps. No reducedness, finiteness, etaleness or
unproved numerical torsion count is inserted into the kernel scheme. -/
@[expose] def kernelOriginalEquiv :
    KernelPoints τ hτ n (Spec (CommRingCat.of ℂ)) (𝟙 _) ≃ {q : Base τ // n • q=0} :=
  (pointsEquiv τ hτ n (𝟙 _)).trans (originalTorsionEquiv τ hτ n).symm

lemma kernelOriginal_point (p : KernelPoints τ hτ n (Spec (CommRingCat.of ℂ)) (𝟙 _)) :
    p.val≫inclusion τ hτ n=
      PELOriginalCandidateComplexPoints318.candidateComplexPoint τ hτ
        (kernelOriginalEquiv τ hτ n p).val := by
  change (pointsEquiv τ hτ n (𝟙 _) p).val.val=
    (originalAddEquiv τ hτ ((originalAddEquiv τ hτ).symm
      (pointsEquiv τ hτ n (𝟙 _) p).val)).val
  rw [AddEquiv.apply_symm_apply]
end PELOriginalTorsionPointComparison318
