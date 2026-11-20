module
public import SelectedOriginalRationalOrdinaryRoot318
public import EtaleNormalization318
public section
noncomputable section

open Polynomial
open scoped TensorProduct nonZeroDivisors
open SelectedOriginalRationalOrdinary318 SelectedOriginalRationalOrdinaryRoot318
open SelectedRationalGenericFromComplex318

namespace SelectedOriginalRationalOrdinaryIntegral318

attribute [local instance] SelectedOriginalRationalOrdinary318.ratscalar

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])

abbrev B := ordinaryRoot N p
abbrev K := genericRoot N p
abbrev Tensor := B N p ⊗[Base] QJ

/-- The full generic algebra, with the original x and the original scalar
action; only the standard order of the tensor factors is changed. -/
@[expose] def tensorComparison : Tensor N p ≃ₐ[Base] K N p :=
  (Algebra.TensorProduct.comm Base (B N p) QJ).trans ((genericEquiv N p).restrictScalars Base)

/-- Inclusion of the original ordinary order in its own full generic algebra. -/
@[expose] def genericEmbedding : B N p →+* K N p :=
  (tensorComparison N p).toRingHom.comp (algebraMap (B N p) (Tensor N p))

theorem genericEmbedding_x :
    genericEmbedding N p (AdjoinRoot.root (ordinaryPolynomial N p)) =
      AdjoinRoot.root (p.map (rationalGenericMap N)) := by
  change (genericEquiv N p)
    ((Algebra.TensorProduct.comm Base (B N p) QJ)
      (algebraMap (B N p) (Tensor N p) (AdjoinRoot.root (ordinaryPolynomial N p)))) = _
  rw [Algebra.TensorProduct.algebraMap_apply,Algebra.TensorProduct.comm_tmul]
  exact genericEquiv_x N p

/-- The ordinary rational ring is the entire integral closure in
the SAME generic algebra. The smooth-base-change calculation uses
the derivative unit on this very root chart, not on an unrelated cover. -/
theorem actual_integralClosure (hp : p.Monic)
    (hd : IsUnit (AdjoinRoot.mk p p.derivative)) :
    letI : Algebra (B N p) (K N p) := (genericEmbedding N p).toAlgebra
    IsIntegralClosure (B N p) Base (K N p) := by
  letI : Algebra (B N p) (K N p) := (genericEmbedding N p).toAlgebra
  letI : IsFractionRing Base QJ := ratFraction
  letI : IsIntegrallyClosed Base :=
    isIntegrallyClosed_of_isLocalization Base (Submonoid.powers denominator) (by
      rintro _ ⟨a,rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero a
        (mul_ne_zero Polynomial.X_ne_zero
          (by simpa using Polynomial.X_sub_C_ne_zero (1728 : ℚ)))))
  letI : Module.Finite Base (B N p) := ordinary_finite N p hp
  letI : Algebra.Etale Base (B N p) := ordinary_etale N p hp hd
  letI : IsIntegralClosure (B N p) Base (Tensor N p) :=
    EtaleNormalization318.smooth_finite_integralClosure
      (R := Base) (S := B N p) (K := QJ)
  let E := tensorComparison N p
  constructor
  · exact E.injective.comp (IsIntegralClosure.algebraMap_injective (B N p) Base (Tensor N p))
  · intro x
    constructor
    · intro hx
      obtain ⟨b,hb⟩ := (IsIntegralClosure.isIntegral_iff
        (A := B N p) (R := Base) (B := Tensor N p)).mp (hx.map E.symm.toAlgHom)
      refine ⟨b,?_⟩
      change E (algebraMap (B N p) (Tensor N p) b) = x
      rw [hb,AlgEquiv.apply_symm_apply]
    · rintro ⟨b,rfl⟩
      have hb : IsIntegral Base (algebraMap (B N p) (Tensor N p) b) :=
        (IsIntegralClosure.isIntegral_iff (A := B N p) (R := Base) (B := Tensor N p)).mpr ⟨b,rfl⟩
      exact hb.map E.toAlgHom

/-- The canonical ordinary-order comparison commutes with the ambient
inclusion in the identical whole generic field, in particular on x. -/
def closureToOrdinary (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative)) :
    integralClosure Base (K N p) ≃ₐ[Base] B N p := by
  letI : Algebra (B N p) (K N p) := (genericEmbedding N p).toAlgebra
  letI : IsIntegralClosure (B N p) Base (K N p) := actual_integralClosure N p hp hd
  exact IsIntegralClosure.equiv Base (integralClosure Base (K N p)) (K N p) (B N p)

theorem closureToOrdinary_value (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (x : integralClosure Base (K N p)) :
    genericEmbedding N p (closureToOrdinary N p hp hd x) = (x : K N p) := by
  letI : Algebra (B N p) (K N p) := (genericEmbedding N p).toAlgebra
  letI : IsIntegralClosure (B N p) Base (K N p) := actual_integralClosure N p hp hd
  exact IsIntegralClosure.algebraMap_equiv Base (integralClosure Base (K N p))
    (K N p) (B N p) x

end SelectedOriginalRationalOrdinaryIntegral318

#print axioms SelectedOriginalRationalOrdinaryIntegral318.genericEmbedding_x
#print axioms SelectedOriginalRationalOrdinaryIntegral318.actual_integralClosure
#print axioms SelectedOriginalRationalOrdinaryIntegral318.closureToOrdinary_value
