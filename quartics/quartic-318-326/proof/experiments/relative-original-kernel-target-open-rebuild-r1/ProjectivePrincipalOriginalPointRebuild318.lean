module
public import ProjectivePrincipalUnitTrivialization318
public section
noncomputable section
namespace ProjectivePrincipalOriginalPointRebuild318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (i : Fin F.size) (S : CommRingCat.{0}) [Algebra R S]
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P i
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P i
local notation "E" => ProjectivePrincipalUnitTrivialization318.trivialization R P i S
local notation "q" => Ideal.Quotient.mkₐ R (ProjectiveParameterSliceAlgebra318.ideal R P i)
lemma backward_original (u : Sˣ) (b : B →ₐ[R] S) :
    (E.symm (u,b)).comp (ProjectiveParameterPrincipalNormalization318.point R P i) =
      ProjectiveParameterUnitAction318.pointScale R P S (u:S) (b.comp q) := by
  apply AlgHom.ext
  intro z
  exact ProjectivePrincipalUnitTrivialization318.backward_include R P i S _ z
/-- The normalized point retains its ACTUAL original parameter. The
missing scalar is precisely the recorded invertible coordinate. -/
lemma original (a : H →ₐ[R] S) :
    a.comp (ProjectiveParameterPrincipalNormalization318.point R P i) =
      ProjectiveParameterUnitAction318.pointScale R P S ((E a).1:S) ((E a).2.comp q) := by
  have h := backward_original R P i S (E a).1 (E a).2
  rw [E.symm_apply_apply] at h
  exact h
end ProjectivePrincipalOriginalPointRebuild318
