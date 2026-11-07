module
public import IntegralDimension318
public import ArithmeticJModel318
public section
noncomputable section
namespace JModelDimension318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section Generic
variable {A C:CommRingCat} {Y:Scheme} (φ:A⟶C) (c:Spec A⟶Y) [IsOpenImmersion c]
  [QuasiCompact (Spec.map φ≫c)] [QuasiSeparated (Spec.map φ≫c)]
theorem dimension_of_factor (f:Spec C⟶Y) [QuasiCompact f] [QuasiSeparated f]
    (hf:f=Spec.map φ≫c) (hinj:Function.Injective φ.hom) :
    ringKrullDim Γ(f.normalization,f.fromNormalization⁻¹ᵁ(c ''ᵁ ⊤))=ringKrullDim A := by
  subst f
  letI:=φ.hom.toAlgebra
  letI:FaithfulSMul A (integralClosure A C):=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A C)).mpr (by
      intro a b hab
      exact hinj (congrArg Subtype.val hab))
  rw [ringKrullDim_eq_of_ringEquiv (NormalChart318.sectionsEquiv φ c)]
  exact IntegralDimension318.dimension_eq A (integralClosure A C)
end Generic

variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

theorem finite_polynomial_injective (hN:N≠0) :
    Function.Injective (ProperOpenJNormalization318.finitePolynomial N B) := by
  have hd:=OpenJNormalModel318.denominator_ne_zero N hN
  letI:IsDomain (OpenJModel318.Base N):=IsLocalization.Away.isDomain _ hd
  exact (FaithfulSMul.algebraMap_injective (OpenJModel318.Base N) B).comp
    (IsLocalization.injective (M:=Submonoid.powers (OpenJModel318.denominator N)) _
      (by rintro x ⟨n,rfl⟩; exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd)))

theorem reciprocal_polynomial_injective (hN:N≠0) :
    Function.Injective (ReciprocalCover318.polynomialMap N B) := by
  have hd:=OpenJNormalModel318.denominator_ne_zero N hN
  have hd':=ReciprocalCover318.denominator_ne_zero N hN
  letI:IsDomain (OpenJModel318.Base N):=IsLocalization.Away.isDomain _ hd
  exact (FaithfulSMul.algebraMap_injective (OpenJModel318.Base N) B).comp
    ((ReciprocalJ318.reciprocalEquiv N).symm.injective.comp
      (IsLocalization.injective (M:=Submonoid.powers (ReciprocalJ318.denominator N)) _
        (by rintro x ⟨n,rfl⟩; exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd'))))

/-- Both actual affine chart rings of the constructed proper normal model
have Krull dimension exactly two, not a supplied surface-dimension premise. -/
theorem chart_dimension_two (hN:N≠0) (j:Fin 2) :
    ringKrullDim (NormalJModel318.chartRing N B j)=2 := by
  fin_cases j
  · exact (dimension_of_factor
      (CommRingCat.ofHom (ReciprocalCover318.polynomialMap N B)) (JLineAtlas318.chart ℤ 0)
      (OpenJProjectiveMap318.coverMap N B) (ReciprocalProjective318.coverMap_infinity N B)
      (reciprocal_polynomial_injective N B hN)).trans IntegralDimension318.integer_polynomial_dimension
  · exact (dimension_of_factor
      (CommRingCat.ofHom (ProperOpenJNormalization318.finitePolynomial N B)) (JLineAtlas318.chart ℤ 1)
      (OpenJProjectiveMap318.coverMap N B) (ProperOpenJNormalization318.finite_factor N B)
      (finite_polynomial_injective N B hN)).trans IntegralDimension318.integer_polynomial_dimension
end JModelDimension318
