module
public import FieldKernelLinearPoints318
public import AlgebraPointEquivalence318
public section
noncomputable section
namespace FieldKernelParameterAlgebraIso318
variable (K P Q : Type) [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q] (d : P →ₗ[K] Q)
  [Module.Finite K P] [Module.Finite K Q]

/-- Genuine inverse ALGEBRA maps from the natural bijections on ALL
coefficient algebras, evaluated at the two actual identity points. -/
@[expose] def equivalence : ProjectiveKernelParameter318.algebra K P Q d ≃ₐ[K]
    ProjectiveSectionParameter318.algebra K (LinearMap.ker d) :=
  AlgebraPointEquivalence318.algebraEquiv K _ _ (FieldKernelLinearPoints318.points K P Q d)
    (FieldKernelLinearPoints318.natural K P Q d)

lemma point_value (S : Type) [CommRing S] [Algebra K S]
    (a : ProjectiveKernelParameter318.algebra K P Q d →ₐ[K] S) :
    FieldKernelLinearPoints318.points K P Q d S a=a.comp (equivalence K P Q d).symm.toAlgHom :=
  AlgebraPointEquivalence318.evaluate K _ _ (FieldKernelLinearPoints318.points K P Q d)
    (FieldKernelLinearPoints318.natural K P Q d) S a
end FieldKernelParameterAlgebraIso318
