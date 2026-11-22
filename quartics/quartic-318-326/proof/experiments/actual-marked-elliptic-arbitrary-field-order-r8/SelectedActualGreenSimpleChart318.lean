module
public import SelectedActualPrimitiveKernelAffine318
public import SelectedPrimitiveSimpleChart318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
open SelectedPrimitiveFixedX318 SelectedPrimitiveXCharacteristic318
open SelectedActualPrimitiveKernelAffine318

namespace SelectedActualGreenSimpleChart318

/-- The original level-N primitive chart has the actual sign-fixed
powers basis on the literal x. Its canonical characteristic equation
is monic and the derivative is a unit in the same monogenic algebra.
The proved finite/étale kernel is installed on the same zero pullback;
no kernel or coordinate-ring hypotheses are supplied. -/
theorem literal_level_simple (N : ℕ) (hN : 2 < N) :
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
               IsUnit (AdjoinRoot.mk p p.derivative)) := by
  letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
  letI : Etale (kernelProjection N N) := (native_level_instances N).2
  have h1 : 1 < N := by omega
  have h0 : N ≠ 0 := by omega
  obtain ⟨I,e,he,hbase,hfin,het,σ,hσ,hinv⟩ := actual_level_affine_sign N h1
  letI : Module.Finite (R N) (D N ⧸ I) := hfin
  letI : Algebra.Etale (R N) (D N ⧸ I) := het
  obtain ⟨pb,hg,hp⟩ := SelectedPrimitiveSimpleChart318.characteristic_simple N I σ hσ hinv h0
  refine ⟨I,e,he,hbase,σ,hσ,hinv,pb,hg,?_⟩
  letI : Module.Free (R N) (fixed N I σ) := Module.Free.of_basis pb.basis
  letI : Module.Finite (R N) (fixed N I σ) := pb.finite
  let p := charPolynomial N I σ hσ
  obtain ⟨hm,ep,hx,hu⟩ := hp
  change p.Monic at hm
  change ep (AdjoinRoot.root p)=coordinate N I σ hσ at hx
  change IsUnit (aeval (coordinate N I σ hσ) p.derivative) at hu
  refine ⟨p,rfl,hm,ep,hx,?_⟩
  have hv := hu.map ep.symm.toRingHom
  have heval : ep.symm.toAlgHom (aeval (coordinate N I σ hσ) p.derivative) =
      AdjoinRoot.mk p p.derivative := by
    rw [← hx,← Polynomial.aeval_algHom_apply]
    change aeval (ep.symm (ep (AdjoinRoot.root p))) p.derivative = _
    rw [AlgEquiv.symm_apply_apply,AdjoinRoot.aeval_eq]
  change IsUnit (ep.symm.toAlgHom (aeval (coordinate N I σ hσ) p.derivative)) at hv
  exact heval ▸ hv

end SelectedActualGreenSimpleChart318

#print axioms SelectedActualGreenSimpleChart318.literal_level_simple
