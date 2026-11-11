module
public import OriginalParameterFormalSmooth318
public import ProjectiveSymmetricPresentation318
public section
noncomputable section
namespace OriginalParameterSliceSmooth318
universe u
variable (R P : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P

instance finitePresentation (i : Fin F.size) :
    Algebra.FinitePresentation R (ProjectiveParameterSliceAlgebra318.algebra R P i) := by
  letI : Module.Finite R (Module.Dual R P) :=
    (FiniteProjectiveDualRetract318.properties R P F).1
  letI : Module.Projective R (Module.Dual R P) :=
    (FiniteProjectiveDualRetract318.properties R P F).2
  letI : Algebra.FinitePresentation R (ProjectiveSectionParameter318.algebra R P) :=
    ProjectiveSymmetricPresentation318.finitePresentation R (Module.Dual R P)
      (FiniteProjectiveEvaluationFrame318.frame R (Module.Dual R P))
  exact Algebra.FinitePresentation.quotient
    (Submodule.fg_span (Set.finite_singleton (ProjectiveParameterZeroCoordinates318.coordinate R P i-1)))

/-- Genuine smoothness of EVERY actual normalized parameter slice:
finite presentation and infinitesimal lifting are both constructed over
the ORIGINAL arbitrary base, without a hidden free-module hypothesis. -/
instance smooth (i : Fin F.size) :
    Algebra.Smooth R (ProjectiveParameterSliceAlgebra318.algebra R P i) := ⟨inferInstance,inferInstance⟩
end OriginalParameterSliceSmooth318
