module
public import SelectedActualGreenSimpleChart318
public import SelectedActualComplexWholeRootField318
import all SelectedActualComplexWholeRootField318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedActualPrimitiveKernelAffine318 SelectedActualGreenSimpleChart318
open SelectedActualComplexOrdinaryScalar318

namespace SelectedGreenLiteralWholeComplexField318

/-- The whole complex generic affine root algebra is a field on the
identical kernel quotient, involution, marked x and characteristic
polynomial supplied by the proved literal simple chart. The proof
uses the full ordinary marked-period image, not a selected factor. -/
theorem literal_level_whole_field (N : ℕ) (hN : 2 < N) :
    letI : NeZero N := ⟨by omega⟩
    letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
    letI : Etale (kernelProjection N N) := (native_level_instances N).2
    ∃ (I : Ideal (D N)) (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I))),
      intoAffine N N (by omega : 1 < N) =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I) ∧
      ∃ (σ : (D N ⧸ I) →ₐ[R N] (D N ⧸ I))
        (hσ : σ.comp (q N I) = (q N I).comp (sign N)),
        σ.comp σ = AlgHom.id (R N) (D N ⧸ I) ∧
        ∃ pb : PowerBasis (R N) (fixed N I σ), pb.gen = coordinate N I σ hσ ∧
          (letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
           letI : Module.Finite (R N) (fixed N I σ) := pb.finite
           ∃ p : (R N)[X], p=charPolynomial N I σ hσ ∧ p.Monic ∧
             ∃ ep : AdjoinRoot p ≃ₐ[R N] fixed N I σ,
               ep (AdjoinRoot.root p)=coordinate N I σ hσ ∧
               IsUnit (AdjoinRoot.mk p p.derivative) ∧
               IsField (AdjoinRoot (SelectedComplexOrdinaryOneField318.genericPolynomial
                 (p.map (toComplex N))))) := by
  letI : NeZero N := ⟨by omega⟩
  letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
  letI : Etale (kernelProjection N N) := (native_level_instances N).2
  obtain ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,hchart⟩ := literal_level_simple N hN
  letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
  letI : Module.Finite (R N) (fixed N I σ) := pb.finite
  obtain ⟨p,hChar,hMonic,ep,hroot,hder⟩ := hchart
  have hf : IsField (AdjoinRoot (SelectedComplexOrdinaryOneField318.genericPolynomial
        (p.map (toComplex N)))) :=
    SelectedActualComplexWholeRootField318.actual_simple_root_field N hN I e hb he
      σ hσ p ep hroot hMonic hder
  exact ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,p,hChar,hMonic,ep,hroot,hder,hf⟩

end SelectedGreenLiteralWholeComplexField318

#print axioms SelectedGreenLiteralWholeComplexField318.literal_level_whole_field
