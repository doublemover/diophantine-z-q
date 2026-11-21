module
public import SelectedGreenLiteralWholeComplexField318
public import SelectedRationalGenericFromComplex318
public import SelectedLiteralRatFuncScalar318
public import Mathlib.NumberTheory.NumberField.Basic
import all SelectedGreenLiteralWholeComplexField318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedActualPrimitiveKernelAffine318 SelectedActualComplexOrdinaryScalar318
open SelectedGreenLiteralWholeComplexField318 SelectedRationalGenericFromComplex318
open SelectedComplexGenericRatFunc318 SelectedComplexOrdinaryOneField318

namespace SelectedActualWholeNumberFieldRoot318

variable (L : Type*) [Field L] [NumberField L]

/-- Literal coefficient extension from the original localized chart
to this actual evaluation field L(J). -/
@[expose] def coefficientMap (N : ℕ) [NeZero N] : R N→+*RatFunc L :=
  (SelectedLiteralRatFuncScalar318.map (algebraMap ℚ L)).comp (rationalGenericMap N)

theorem coefficient_j (N : ℕ) [NeZero N] :
    coefficientMap L N (OpenJModel318.jCoord N)=(RatFunc.X:RatFunc L) := by
  rw [coefficientMap,RingHom.comp_apply,rationalGenericMap_j,SelectedLiteralRatFuncScalar318.map_X]

@[expose] def intoComplexGeneric (ι : L→+*ℂ) : RatFunc L→+*Generic := by
  letI : Algebra SelectedComplexOrdinaryBase318.Base (RatFunc ℂ) := ratscalar
  exact ratEquiv.symm.toRingHom.comp (SelectedLiteralRatFuncScalar318.map ι)

theorem intoComplex_j (ι : L→+*ℂ) :
    intoComplexGeneric L ι (RatFunc.X:RatFunc L) =
      algebraMap SelectedComplexOrdinaryBase318.Base Generic SelectedComplexOrdinaryBase318.jCoord := by
  letI : Algebra SelectedComplexOrdinaryBase318.Base (RatFunc ℂ) := ratscalar
  apply ratEquiv.injective
  change ratEquiv (ratEquiv.symm (SelectedLiteralRatFuncScalar318.map ι (RatFunc.X:RatFunc L))) = _
  rw [AlgEquiv.apply_symm_apply,SelectedLiteralRatFuncScalar318.map_X,
    ratEquiv_literal_j,RatFunc.algebraMap_X]

/-- The full original-localized and complex coefficient maps agree,
not just a specified root value. This pins the orientation of J in
the evaluation number field and retains the original polynomial. -/
theorem same_composite (N : ℕ) [NeZero N] (ι : L→+*ℂ) :
    (intoComplexGeneric L ι).comp (coefficientMap L N) =
      (algebraMap SelectedComplexOrdinaryBase318.Base Generic).comp (toComplex N) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator N))
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · change intoComplexGeneric L ι (coefficientMap L N (OpenJModel318.jCoord N)) =
      algebraMap SelectedComplexOrdinaryBase318.Base Generic (toComplex N (OpenJModel318.jCoord N))
    rw [coefficient_j,intoComplex_j,toComplex_j]

/-- Absolute irreducibility over the verified complex ordinary field
reflects down to the whole L(J)-root algebra for the same p. This
works for any chosen archimedean embedding, not a chosen factor. -/
theorem whole_isField (N : ℕ) [NeZero N] (ι : L→+*ℂ) (p : (R N)[X]) (hp : p.Monic)
    (hC : IsField (AdjoinRoot (genericPolynomial (p.map (toComplex N))))) :
    IsField (AdjoinRoot (p.map (coefficientMap L N))) := by
  letI : IsDomain SelectedComplexOrdinaryBase318.Base := coefficient_domain
  have hC' := AdjoinRoot.isField_iff_irreducible.mp hC
  change Irreducible ((p.map (toComplex N)).map
    (algebraMap SelectedComplexOrdinaryBase318.Base Generic)) at hC'
  apply AdjoinRoot.isField_iff_irreducible.mpr
  apply (hp.map _).isPrimitive.irreducible_of_irreducible_map_of_injective
    (intoComplexGeneric L ι).injective
  simpa only [Polynomial.map_map,same_composite L N ι] using hC'

/-- No rational or number-field factor is chosen after the original
marked-period proof. The entire root algebra in L(J) is a field. -/
theorem literal_level_whole_numberField (N : ℕ) (hN : 2<N) (ι : L→+*ℂ) :
    letI : NeZero N := ⟨by omega⟩
    letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
    letI : Etale (kernelProjection N N) := (native_level_instances N).2
    ∃ (I : Ideal (D N)) (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I))),
      intoAffine N N (Nat.lt_of_succ_lt hN) =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I) ∧
      ∃ (σ : (D N ⧸ I) →ₐ[R N] (D N ⧸ I))
        (hσ : σ.comp (q N I)=(q N I).comp (sign N)),
        σ.comp σ=AlgHom.id (R N) (D N ⧸ I) ∧
        ∃ pb : PowerBasis (R N) (fixed N I σ), pb.gen=coordinate N I σ hσ ∧
          (letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
           letI : Module.Finite (R N) (fixed N I σ) := pb.finite
           ∃ p : (R N)[X], p=charPolynomial N I σ hσ ∧ p.Monic ∧
             ∃ ep : AdjoinRoot p ≃ₐ[R N] fixed N I σ,
               ep (AdjoinRoot.root p)=coordinate N I σ hσ ∧
               IsUnit (AdjoinRoot.mk p p.derivative) ∧
               IsField (AdjoinRoot (p.map (coefficientMap L N)))) := by
  letI : NeZero N := ⟨by omega⟩
  letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
  letI : Etale (kernelProjection N N) := (native_level_instances N).2
  obtain ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,hchart⟩ := literal_level_whole_field N hN
  letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
  letI : Module.Finite (R N) (fixed N I σ) := pb.finite
  obtain ⟨p,hchar,hp,ep,her,hder,hC⟩ := hchart
  exact ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,p,hchar,hp,ep,her,hder,whole_isField L N ι p hp hC⟩

end SelectedActualWholeNumberFieldRoot318

#print axioms SelectedActualWholeNumberFieldRoot318.whole_isField
#print axioms SelectedActualWholeNumberFieldRoot318.literal_level_whole_numberField
