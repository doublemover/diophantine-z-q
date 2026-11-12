module
public import ProjectiveSectionParameter318
public import ProjectiveSymmetricPresentation318
public import FiniteProjectiveDualRetract318
public section
noncomputable section
namespace ProjectiveSectionFinitePresentation318
universe u
variable (R P : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [hfinite : Module.Finite R P] [hprojective : Module.Projective R P]

include hfinite hprojective in
/-- Finite presentation of the ACTUAL symmetric-dual parameter over an
arbitrary ring, from the original finite projective retract. No basis is assumed. -/
instance finitePresentation : Algebra.FinitePresentation R (ProjectiveSectionParameter318.algebra R P) := by
  let F := FiniteProjectiveEvaluationFrame318.frame R P
  letI : Module.Finite R (Module.Dual R P) := (FiniteProjectiveDualRetract318.properties R P F).1
  letI : Module.Projective R (Module.Dual R P) := (FiniteProjectiveDualRetract318.properties R P F).2
  exact ProjectiveSymmetricPresentation318.finitePresentation R (Module.Dual R P)
    (FiniteProjectiveEvaluationFrame318.frame R (Module.Dual R P))
end ProjectiveSectionFinitePresentation318
