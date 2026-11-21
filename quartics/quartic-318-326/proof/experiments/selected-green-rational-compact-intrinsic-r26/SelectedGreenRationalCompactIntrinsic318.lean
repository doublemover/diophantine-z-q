module
public import SelectedGreenLiteralRationalCompact318
public import SelectedRationalCompactIntrinsicCoefficient318
import all SelectedGreenLiteralRationalCompact318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedActualPrimitiveKernelAffine318 SelectedGreenLiteralWholeRationalField318
open SelectedRationalRootCompactInstall318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryGeometry318
open SelectedOriginalCompactClassicalDifferentials318 SelectedIntrinsicGlobalToAffine318
open SelectedRationalCompactIntrinsicCoefficient318

namespace SelectedGreenRationalCompactIntrinsic318

/-- Return the ORIGINAL selected rational compact with its actual
intrinsic ordinary restriction in the literally normalized dJ frame.
From the whole-complex-field theorem, no polynomial factor, rational
surface, coefficient ring, differential, or reparametrization is chosen. -/
theorem literal_rational_compact_intrinsic (N : ℕ) (hN : 2<N) :
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
                 IsProper (compactStructure N p hf) ∧
                 IsIntegral (compact N p hf) ∧
                 (∀ x : compact N p hf, IsIntegrallyClosed ((compact N p hf).presheaf.stalk x)) ∧
                 (∃ u : Spec (CommRingCat.of (ordinaryRoot N p)) ≅ (actualOpen N p hf).toScheme,
                   u.hom ≫ (actualOpen N p hf).ι=ordinaryEmbedding N p hf hp hd) ∧
                 ∃ hq : ordinaryEmbedding N p hf hp hd ≫ compactStructure N p hf =
                    Spec.algebraMap ℚ (ordinaryRoot N p),
                   ordinaryFrame N p hp hd (KaehlerDifferential.D ℚ (ordinaryRoot N p)
                     (jInRoot N p))=1 ∧
                   ∀ w : RationalSections N p hf,
                       rationalCoefficient N p hp hd hf w =
                         ordinaryFrame N p hp hd
                           (restrict (ordinaryEmbedding N p hf hp hd) (compactStructure N p hf) hq w)) := by
  letI : NeZero N := ⟨by omega⟩
  letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
  letI : Etale (kernelProjection N N) := (native_level_instances N).2
  obtain ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,p,hchar,hp,ep,hroot,hd,hf,hfin,hproper,hint,hnorm,hopen⟩ :=
    SelectedGreenLiteralRationalCompact318.literal_level_rational_compact N hN
  letI : Fact p.Monic := ⟨hp⟩
  refine ⟨I,e,he,hb,σ,hσ,hinv,pb,hpb,p,hchar,hp,ep,hroot,hd,hf,hfin,hproper,hint,hnorm,hopen,
    actual_ordinary_Q N p hd hf,ordinaryFrame_j N p hp hd,?_⟩
  exact rationalCoefficient_apply N p hp hd hf _

end SelectedGreenRationalCompactIntrinsic318

#print axioms SelectedGreenRationalCompactIntrinsic318.literal_rational_compact_intrinsic
