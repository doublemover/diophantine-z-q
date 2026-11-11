module
public import ProjectiveNormalizedSliceSmooth318
public import ProjectiveParameterSliceAlgebra318
public import FiniteProjectiveDualRetract318
public section
noncomputable section
namespace OriginalParameterFormalSmooth318
universe u
variable (R P : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P

/-- EVERY literal coefficient-one slice of the ORIGINAL finite-projective
section parameter is formally smooth. The dual module is projective by
its actual finite dual-frame retract, not by choosing a free basis. -/
instance formallySmooth (i : Fin F.size) :
    Algebra.FormallySmooth R (ProjectiveParameterSliceAlgebra318.algebra R P i) := by
  letI : Module.Projective R (Module.Dual R P) :=
    (FiniteProjectiveDualRetract318.properties R P F).2
  exact ProjectiveNormalizedSliceSmooth318.formallySmooth R (Module.Dual R P) (F.coordinate i)
end OriginalParameterFormalSmooth318
