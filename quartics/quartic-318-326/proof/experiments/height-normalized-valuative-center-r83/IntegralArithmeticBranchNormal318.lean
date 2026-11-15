module
public import IntegralSourceArithmeticDomain318
public import IntegralBranchCoordinates318
public import SmoothGenericField318
public import NormalitySpanDescent318
public section
noncomputable section
namespace IntegralArithmeticBranchNormal318
open Polynomial IntegralSourceBranches318
open scoped nonZeroDivisors
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R] [IsDomain R] [Algebra R ℚ]
  [IsIntegrallyClosed R] (c : Fin 4 → Rˣ)

/-- These are the actual distinct original contact labels in the arithmetic
coefficient ring, as witnessed by its specified map to Q. -/
theorem other_distinct (i : Fin 4) (j : Fin 3) :
    contacts R i ≠ otherContact R i j := by
  intro he
  have hq := congrArg (algebraMap R ℚ) he
  simp only [otherContact,IntegralSourceArithmeticDomain318.contacts_map] at hq
  have hi := LinearContactSquareclass318.contacts_injective hq
  have hz : (0 : Fin 4) = j.succ :=
    FourRootPivot318.indices_injective i ((FourRootPivot318.indices_zero i).trans hi)
  exact Fin.succ_ne_zero j hz.symm

theorem source_denominator_ne_zero (i : Fin 4) :
    IntegralBranchDenominatorCover318.denominator R c i ≠ 0 := by
  letI : Module.FaithfullyFlat R[X] (SourceOrder R c) :=
    FourRootOrder318.faithfullyFlat (coefficient R c)
  have hp : IntegralBranchDenominatorCover318.twisted R c i ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr (c (FourRootPivot318.indices i j.succ)).ne_zero
    · exact Polynomial.X_sub_C_ne_zero _
  simpa only [IntegralBranchDenominatorCover318.denominator,map_zero] using
    (FaithfulSMul.algebraMap_injective R[X] (SourceOrder R c)).ne hp

theorem branch_domain (i : Fin 4) : IsDomain (BranchBase R c i) :=
  Function.Injective.isDomain
    (LinearRootCoordinate318.coordinateEquiv (c i) (contacts R i)).toRingHom
    (LinearRootCoordinate318.coordinateEquiv (c i) (contacts R i)).injective

theorem branch_normal (i : Fin 4) : IsIntegrallyClosed (BranchBase R c i) :=
  IsIntegrallyClosed.of_equiv
    (LinearRootCoordinate318.coordinateEquiv (c i) (contacts R i)).symm.toRingEquiv

theorem base_denominator_ne_zero (i : Fin 4) :
    IntegralBranchChart318.denominator (c i) (contacts R i)
      (otherTwist R c i) (otherContact R i) ≠ 0 := by
  intro hz
  have he := IntegralBranchChart318.denominator_at_branch
    (c i) (contacts R i) (otherTwist R c i) (otherContact R i)
  rw [hz,map_zero] at he
  apply (Finset.prod_ne_zero_iff.mpr (fun j _ =>
    mul_ne_zero (otherTwist R c i j).ne_zero (sub_ne_zero.mpr (other_distinct R i j))))
  exact he.symm

theorem open_base_domain (i : Fin 4) : IsDomain (OpenBase R c i) := by
  letI := branch_domain R c i
  exact Localization.Away.isDomain (base_denominator_ne_zero R c i)

theorem open_base_normal (i : Fin 4) : IsIntegrallyClosed (OpenBase R c i) := by
  letI := branch_domain R c i
  letI := branch_normal R c i
  apply isIntegrallyClosed_of_isLocalization (OpenBase R c i)
    (Submonoid.powers (IntegralBranchChart318.denominator (c i) (contacts R i)
      (otherTwist R c i) (otherContact R i)))
  rintro _ ⟨n,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (base_denominator_ne_zero R c i))

theorem localized_domain (hR : Function.Injective (algebraMap R ℚ)) (i : Fin 4) :
    IsDomain (IntegralBranchCoordinates318.B R c i) := by
  letI := IntegralSourceArithmeticDomain318.source_domain R c hR
  exact Localization.Away.isDomain (source_denominator_ne_zero R c i)

theorem chart_domain (hR : Function.Injective (algebraMap R ℚ)) (i : Fin 4) :
    IsDomain (OpenOrder R c i) := by
  letI := localized_domain R c hR i
  exact Function.Injective.isDomain
    (IntegralBranchLocalization318.sourceLocalizationEquiv R c i).symm.toRingHom
    (IntegralBranchLocalization318.sourceLocalizationEquiv R c i).symm.injective

/-- Every whole original finite branch chart is normal over the original
normal arithmetic coefficient base; no normal component is selected. -/
theorem chart_normal (hR : Function.Injective (algebraMap R ℚ))
    (h2 : IsUnit (2 : R)) (i : Fin 4) : IsIntegrallyClosed (OpenOrder R c i) := by
  letI := open_base_domain R c i
  letI := open_base_normal R c i
  letI := chart_domain R c hR i
  letI : Module.Finite (OpenBase R c i) (OpenOrder R c i) := (finite_free_etale R c h2 i).1
  letI : Algebra.Etale (OpenBase R c i) (OpenOrder R c i) := (finite_free_etale R c h2 i).2.2
  exact SmoothGenericField318.smooth_integrallyClosed
    (R := OpenBase R c i) (K := FractionRing (OpenBase R c i)) (B := OpenOrder R c i)

theorem localized_normal (hR : Function.Injective (algebraMap R ℚ))
    (h2 : IsUnit (2 : R)) (i : Fin 4) :
    IsIntegrallyClosed (IntegralBranchCoordinates318.B R c i) := by
  letI := chart_normal R c hR h2 i
  exact IsIntegrallyClosed.of_equiv
    (IntegralBranchLocalization318.sourceLocalizationEquiv R c i).symm.toRingEquiv

/-- Actual normality of the whole arithmetic source, descended from all four
original branch localizations covering it on the good coefficient base. -/
theorem source_normal (hR : Function.Injective (algebraMap R ℚ))
    (h2 : IsUnit (2 : R))
    (hN : IsUnit (IntegralBranchDenominatorCover318.separationInteger : R)) :
    IsIntegrallyClosed (SourceOrder R c) := by
  letI := IntegralSourceArithmeticDomain318.source_domain R c hR
  exact NormalitySpanDescent318.of_principal_cover
    (IntegralBranchDenominatorCover318.denominator R c)
    (IntegralBranchDenominatorCover318.span_top R c hN) (localized_normal R c hR h2)
end IntegralArithmeticBranchNormal318
