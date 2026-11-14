module
public import ProjectiveSymmetricPresentation318
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Smooth.Basic
public section
noncomputable section
namespace ProjectiveSymmetricSmooth318
universe u
variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
  [hprojective : Module.Projective R M]

include hprojective in
/-- Actual infinitesimal lifting for the symmetric algebra of a
projective module, by lifting the literal underlying linear map. -/
instance formallySmooth : Algebra.FormallySmooth R (SymmetricAlgebra R M) := by
  apply Algebra.FormallySmooth.of_comp_surjective
  intro S _ _ I hI f
  let q := Ideal.Quotient.mkₐ R I
  let l := f.toLinearMap.comp (SymmetricAlgebra.ι R M)
  obtain ⟨g,hg⟩ := Module.projective_lifting_property q.toLinearMap l Ideal.Quotient.mk_surjective
  refine ⟨SymmetricAlgebra.lift g,?_⟩
  apply SymmetricAlgebra.algHom_ext
  ext x
  change q (SymmetricAlgebra.lift g (SymmetricAlgebra.ι R M x))=l x
  rw [SymmetricAlgebra.lift_ι_apply]
  exact LinearMap.congr_fun hg x

variable [hfinite : Module.Finite R M]
include hprojective hfinite in
/-- Formal lifting and the actual finite retract presentation together
give genuine algebraic smoothness over arbitrary original base rings. -/
instance smooth : Algebra.Smooth R (SymmetricAlgebra R M) := by
  letI : Algebra.FinitePresentation R (SymmetricAlgebra R M) :=
    ProjectiveSymmetricPresentation318.finitePresentation R M
      (FiniteProjectiveEvaluationFrame318.frame R M)
  exact ⟨inferInstance,inferInstance⟩
end ProjectiveSymmetricSmooth318
