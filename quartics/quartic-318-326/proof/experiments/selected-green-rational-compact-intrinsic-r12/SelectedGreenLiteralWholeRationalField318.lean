module
public import SelectedGreenLiteralWholeComplexField318
public import SelectedRationalGenericFromComplex318
import all SelectedGreenLiteralWholeComplexField318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedActualPrimitiveKernelAffine318 SelectedActualComplexOrdinaryScalar318
open SelectedGreenLiteralWholeComplexField318 SelectedRationalGenericFromComplex318

namespace SelectedGreenLiteralWholeRationalField318

/-- Reflect the field property of that entire complex generic algebra,
on its literal monic original polynomial, to the whole Q(J) algebra.
No primitive factor, point, or alternative abscissa is chosen. -/
theorem reflect_selected {N : ℕ} [NeZero N] (p : (R N)[X]) (hp : p.Monic)
    (hC : IsField (AdjoinRoot (SelectedComplexOrdinaryOneField318.genericPolynomial
      (p.map (toComplex N))))) :
    IsField (AdjoinRoot (p.map (rationalGenericMap N))) := by
  change IsField (AdjoinRoot ((p.map (toComplex N)).map
    (algebraMap SelectedComplexOrdinaryBase318.Base SelectedComplexOrdinaryOneField318.Generic))) at hC
  rw [Polynomial.map_map] at hC
  exact rational_isField N p hp hC

/-- The literal finite-rational field transport is produced from the
same chosen full ordinary generation of the primitive scheme. In
particular the finite-flat/étale kernel or a field is not an input. -/
theorem literal_level_rational_field (N : ℕ) (hN : 2 < N) :
    letI : NeZero N := ⟨by omega⟩
    letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
    letI : Etale (kernelProjection N N) := (native_level_instances N).2
    ∃ (I : Ideal (D N)) (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I))),
      intoAffine N N (Nat.lt_of_succ_lt hN) =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I) ∧
      ∃ (σ : (D N ⧸ I) →ₐ[R N] (D N ⧸ I))
        (hσ : σ.comp (q N I)=(q N I).comp (sign N)),
        σ.comp σ = AlgHom.id (R N) (D N ⧸ I) ∧
        ∃ pb : PowerBasis (R N) (fixed N I σ), pb.gen=coordinate N I σ hσ ∧
          (letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
           letI : Module.Finite (R N) (fixed N I σ) := pb.finite
           ∃ p : (R N)[X], p=charPolynomial N I σ hσ ∧ p.Monic ∧
             ∃ ep : AdjoinRoot p ≃ₐ[R N] fixed N I σ,
               ep (AdjoinRoot.root p)=coordinate N I σ hσ ∧
               IsUnit (AdjoinRoot.mk p p.derivative) ∧
               IsField (AdjoinRoot (p.map (rationalGenericMap N)))) := by
  letI : NeZero N := ⟨by omega⟩
  letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
  letI : Etale (kernelProjection N N) := (native_level_instances N).2
  obtain ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,hchart⟩ := literal_level_whole_field N hN
  letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
  letI : Module.Finite (R N) (fixed N I σ) := pb.finite
  obtain ⟨p,hchar,hp,ep,her,hder,hC⟩ := hchart
  exact ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,p,hchar,hp,ep,her,hder,reflect_selected p hp hC⟩

end SelectedGreenLiteralWholeRationalField318

#print axioms SelectedGreenLiteralWholeRationalField318.reflect_selected
#print axioms SelectedGreenLiteralWholeRationalField318.literal_level_rational_field
