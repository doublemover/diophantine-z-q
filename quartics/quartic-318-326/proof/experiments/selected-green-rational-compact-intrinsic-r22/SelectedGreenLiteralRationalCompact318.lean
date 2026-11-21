module
public import SelectedGreenLiteralWholeRationalField318
public import SelectedOriginalRationalOrdinaryGeometry318
import all SelectedGreenLiteralWholeRationalField318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedActualPrimitiveKernelAffine318 SelectedGreenLiteralWholeRationalField318
open SelectedRationalRootCompactInstall318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryGeometry318 SelectedOriginalRationalOrdinaryIntegral318

namespace SelectedGreenLiteralRationalCompact318

/-- Attach the existing actual relative normalization to the one
proved whole rational field. The original primitive quotient, x,
monic characteristic p, and literal j-coordinate are not re-selected.
The classical moduli and Hodge identifications remain separate. -/
theorem literal_level_rational_compact (N : ℕ) (hN : 2<N) :
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
           ∃ p : (R N)[X], p=charPolynomial N I σ hσ ∧ ∃ hp : p.Monic,
             ∃ ep : AdjoinRoot p ≃ₐ[R N] fixed N I σ,
               ep (AdjoinRoot.root p)=coordinate N I σ hσ ∧
               ∃ hd : IsUnit (AdjoinRoot.mk p p.derivative),
               ∃ hf : IsField (genericRoot N p),
                 IsFinite (compactJ N p hf) ∧
                 IsProper (compactJ N p hf ≫ ProjectiveJLine318.structureMap ℚ) ∧
                 IsIntegral (compact N p hf) ∧
                 (∀ x : compact N p hf, IsIntegrallyClosed ((compact N p hf).presheaf.stalk x)) ∧
                 ∃ u : Spec (CommRingCat.of (ordinaryRoot N p)) ≅ (actualOpen N p hf).toScheme,
                   u.hom ≫ (actualOpen N p hf).ι=ordinaryEmbedding N p hf hp hd) := by
  letI : NeZero N := ⟨by omega⟩
  letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
  letI : Etale (kernelProjection N N) := (native_level_instances N).2
  obtain ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,hchart⟩ :=
    literal_level_rational_field N hN
  letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
  letI : Module.Finite (R N) (fixed N I σ) := pb.finite
  obtain ⟨p,hchar,hp,ep,hroot,hd,hf⟩ := hchart
  obtain ⟨hfin,hproper,hint,hnorm⟩ := compact_properties N p hp hf
  exact ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,p,hchar,hp,ep,hroot,hd,hf,hfin,hproper,hint,hnorm,
    ordinaryIso N p hf hp hd,ordinaryIso_fac N p hf hp hd⟩

end SelectedGreenLiteralRationalCompact318

#print axioms SelectedGreenLiteralRationalCompact318.literal_level_rational_compact
