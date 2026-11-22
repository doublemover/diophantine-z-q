module

public import SelectedActualOriginalOrdinaryRootBaseComparison318
import all SelectedActualComplexPolynomialOrdinaryBase318
import all SelectedActualComplexOriginalWholeMonicOpening318
import all SelectedActualOriginalOrdinaryScalarBaseComparison318
import all SelectedActualOriginalOrdinaryRootBaseComparison318

public section
noncomputable section

open Polynomial
open scoped TensorProduct Polynomial
open SelectedActualComplexPrincipalOpenScalarChange318
open SelectedActualComplexPolynomialOrdinaryBase318
open SelectedActualComplexOriginalWholeMonicOpening318
open SelectedActualOriginalOrdinaryScalarBaseComparison318
open SelectedActualOriginalOrdinaryRootBaseComparison318

namespace SelectedActualSameOrdinaryRootComplexLinear318

private abbrev d := SelectedOriginalRationalOrdinary318.denominator

private theorem scalarOrdinaryBase_complex (z : ℂ) :
    scalarOrdinaryBase ℚ ℂ d (algebraMap ℂ (ℂ ⊗[ℚ] RQ) z) =
      algebraMap ℂ[X] (complexPolynomialBase ℚ ℂ d) (Polynomial.C z) := by
  let T := ℂ ⊗[ℚ] ℚ[X]
  let W := ℂ ⊗[ℚ] RQ
  let V := complexPolynomialBase ℚ ℂ d
  let e : T ≃ₐ[ℂ] ℂ[X] := (polyEquivTensor' ℚ ℂ).symm
  let hOpen : T →ₐ[ℂ] W := scalarOpenMap ℚ ℂ ℚ[X] RQ
  letI : Algebra T W := hOpen.toRingHom.toAlgebra
  letI : IsLocalization.Away ((1 : ℂ) ⊗ₜ[ℚ] d) W :=
    scalar_change_principal_open ℚ ℂ ℚ[X] RQ d
  have hpow :
      (Submonoid.powers ((1 : ℂ) ⊗ₜ[ℚ] d)).map e.toRingEquiv.toMonoidHom =
        Submonoid.powers (mappedDenominator ℚ ℂ d) := by
    rw [Submonoid.map_powers]
    apply congrArg Submonoid.powers
    change (polyEquivTensor' ℚ ℂ).symm ((1 : ℂ) ⊗ₜ[ℚ] d) = _
    simp only [coe_polyEquivTensor'_symm, polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
  have h := IsLocalization.ringEquivOfRingEquiv_eq (S := W) (Q := V) hpow
    (algebraMap ℂ T z)
  have hw : algebraMap T W (algebraMap ℂ T z) = algebraMap ℂ W z := hOpen.commutes z
  have hv : e.toRingEquiv (algebraMap ℂ T z) = Polynomial.C z := by
    exact e.commutes z
  change scalarOrdinaryBase ℚ ℂ d (algebraMap T W (algebraMap ℂ T z)) =
    algebraMap ℂ[X] V (e.toRingEquiv (algebraMap ℂ T z)) at h
  exact (congrArg (scalarOrdinaryBase ℚ ℂ d) hw).symm.trans
    (h.trans (congrArg (algebraMap ℂ[X] V) hv))

/-- The actual base change comparison also reads the new complex
constant, not only the image of an old rational coefficient. -/
theorem scalarBase_complex (z : ℂ) :
    scalarBase (algebraMap ℂ (ℂ ⊗[ℚ] RQ) z) =
      algebraMap ℂ[X] RC (Polynomial.C z) := by
  unfold scalarBase
  rw [RingEquiv.trans_apply, scalarOrdinaryBase_complex, identifyMappedBase_polynomial]

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

theorem compareOrdinaryRoot_complex (z : ℂ) :
    compareOrdinaryRoot N p (algebraMap ℂ (ℂ ⊗[ℚ] AdjoinRoot (pQ N p)) z) =
      algebraMap ℂ (AdjoinRoot (pC N p)) z := by
  let q := tensorPolynomial ℚ ℂ d (pQ N p)
  let E : ℂ ⊗[ℚ] AdjoinRoot (pQ N p) ≃ₐ[ℂ] AdjoinRoot q :=
    AdjoinRoot.tensorAlgEquiv (pQ N p) q rfl
  have hE : E (algebraMap ℂ _ z) =
      AdjoinRoot.of q (algebraMap ℂ (ℂ ⊗[ℚ] RQ) z) := by
    calc
      _ = algebraMap ℂ (AdjoinRoot q) z := E.commutes z
      _ = _ := by rw [AdjoinRoot.algebraMap_eq']; rfl
  have hTensor :
      (AdjoinRoot.tensorAlgEquiv (pQ N p)
        (tensorPolynomial ℚ ℂ d (pQ N p)) rfl).toRingEquiv
        (algebraMap ℂ (ℂ ⊗[ℚ] AdjoinRoot (pQ N p)) z) =
      AdjoinRoot.of (tensorPolynomial ℚ ℂ d (pQ N p))
        (algebraMap ℂ (ℂ ⊗[ℚ] RQ) z) := hE
  unfold compareOrdinaryRoot originalWholeMonicOpening
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
  rw [hTensor, AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_of,
    AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_of]
  change AdjoinRoot.of (pC N p) (scalarBase (algebraMap ℂ (ℂ ⊗[ℚ] RQ) z)) = _
  rw [scalarBase_complex, AdjoinRoot.algebraMap_eq'] <;> rfl

/-- Same entire comparison, upgraded to its actual complex-linear
algebra map with no transported or assumed scalar action. -/
def compareOrdinaryRootAlg :
    (ℂ ⊗[ℚ] AdjoinRoot (pQ N p)) ≃ₐ[ℂ] AdjoinRoot (pC N p) :=
  { compareOrdinaryRoot N p with
    commutes' := compareOrdinaryRoot_complex N p }

end SelectedActualSameOrdinaryRootComplexLinear318

#print axioms SelectedActualSameOrdinaryRootComplexLinear318.scalarBase_complex
#print axioms SelectedActualSameOrdinaryRootComplexLinear318.compareOrdinaryRoot_complex
