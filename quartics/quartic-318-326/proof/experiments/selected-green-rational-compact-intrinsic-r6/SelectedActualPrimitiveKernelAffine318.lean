module
public import ActualMulKernelFiniteEtale318
public import SelectedPrimitiveAffineSign318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 SelectedPrimitiveOpen318 SelectedPrimitiveAffineSign318
namespace SelectedActualPrimitiveKernelAffine318

/-- Both kernels are literally the same zero pullback of the same
arbitrary-test [N]; the original base already inverts N. No map
comparison using geometric points alone is substituted. -/
theorem native_level_instances (N : ℕ) :
    IsFinite (kernelProjection N N) ∧ Etale (kernelProjection N N) :=
  ActualMulKernelFiniteEtale318.level_kernel_finite_etale N

/-- First semantic kernel client: the actual primitive scheme is
cut out by the very same affine quotient and the literal involution,
with no supplied existence/finite/étale assumptions. -/
theorem actual_level_affine_sign (N : ℕ) (hN : 1 < N) :
    letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
    letI : Etale (kernelProjection N N) := (native_level_instances N).2
    ∃ (I : Ideal (D N)) (e : PrimitiveScheme N N ≅ Spec (CommRingCat.of (D N ⧸ I))),
      intoAffine N N hN = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧
      primitiveProjection N N = e.hom ≫ Spec.algebraMap (R N) (D N ⧸ I) ∧
      Module.Finite (R N) (D N ⧸ I) ∧ Algebra.Etale (R N) (D N ⧸ I) ∧
      ∃ σ : (D N ⧸ I) →ₐ[R N] (D N ⧸ I),
        σ.comp (Ideal.Quotient.mkₐ (R N) I) = (Ideal.Quotient.mkₐ (R N) I).comp (sign N) ∧
        σ.comp σ = AlgHom.id (R N) (D N ⧸ I) := by
  letI : IsFinite (kernelProjection N N) := (native_level_instances N).1
  letI : Etale (kernelProjection N N) := (native_level_instances N).2
  obtain ⟨I,e,he,hb,hfin,het⟩ := affine_quotient N N hN
  obtain ⟨σ,hσ,hinv⟩ := quotient_sign N N hN I e he
  exact ⟨I,e,he,hb,hfin,het,σ,hσ,hinv⟩

end SelectedActualPrimitiveKernelAffine318

#print axioms SelectedActualPrimitiveKernelAffine318.native_level_instances
#print axioms SelectedActualPrimitiveKernelAffine318.actual_level_affine_sign
