module
public import OriginalLineAffineModel318
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.LinearAlgebra.FreeModule.PID

public section
noncomputable section
namespace OriginalLineFiniteFlatPID318
open AlgebraicGeometry CategoryTheory LineSheafClass318
universe u
variable (R B : CommRingCat.{u}) [Algebra R B] (L : Line (Spec B))

/-- The unchanged sections of the original line, with the exact restriction
of scalars along the finite-flat chart algebra map. -/
abbrev pushed : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R B)).obj (OriginalLineAffineModel318.sections B L)

instance : Module B (pushed R B L) :=
  inferInstanceAs (Module B (OriginalLineAffineModel318.sections B L))

instance : IsScalarTower R B (pushed R B L) where
  smul_assoc r b m := by
    have hB : r • b = algebraMap R B r * b := Algebra.smul_def r b
    have hM : r • (b • m) = (algebraMap R B r) • (b • m) :=
      ModuleCat.restrictScalars.smul_def (algebraMap R B)
        (M := OriginalLineAffineModel318.sections B L) r (b • m)
    exact (congrArg (fun z : B => z • m) hB).trans
      ((mul_smul (algebraMap R B r) b m).trans hM.symm)

/-- Actual original sections are finite over the base chart because the
line is finitely presented over the actual finite chart algebra. -/
instance finite [Module.Finite R B] : Module.Finite R (pushed R B L) := by
  letI : Module.FinitePresentation B (pushed R B L) :=
    (OriginalLineAffineModel318.properties B L).1
  letI : Module.Finite B (pushed R B L) := inferInstance
  exact Module.Finite.trans B (pushed R B L)

/-- Actual original sections remain flat on restriction of scalars through
the original flat chart algebra. -/
instance flat [Module.Flat R B] : Module.Flat R (pushed R B L) := by
  letI : Module.Flat B (pushed R B L) :=
    (OriginalLineAffineModel318.properties B L).2.1
  exact Module.Flat.trans R B (pushed R B L)

/-- This produces chart freeness for EVERY actual line, not merely for the
structure sheaf or for a supplied transition matrix. -/
instance free [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R B] [Module.Flat R B] : Module.Free R (pushed R B L) :=
  Module.free_of_finite_type_torsion_free'

variable [IsDomain R] [IsPrincipalIdealRing R] [Module.Finite R B] [Module.Flat R B]

/-- A finite basis of the original pushforward section module. -/
def basis : Module.Basis (Fin (Module.finrank R (pushed R B L))) R (pushed R B L) :=
  Module.finBasis R (pushed R B L)

/-- The resulting coordinates still act on the original section elements. -/
def coordinates : pushed R B L ≃ₗ[R]
    (Fin (Module.finrank R (pushed R B L)) → R) := (basis R B L).equivFun

lemma coordinates_symm_apply (m : pushed R B L) :
    (coordinates R B L).symm (coordinates R B L m) = m :=
  (coordinates R B L).symm_apply_apply m
end OriginalLineFiniteFlatPID318
