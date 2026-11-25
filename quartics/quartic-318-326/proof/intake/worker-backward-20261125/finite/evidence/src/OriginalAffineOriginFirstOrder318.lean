module
public import OriginalAffineOriginCotangent318
public import Mathlib.Algebra.TrivSqZeroExt.Basic

@[expose] public section
noncomputable section

namespace OriginalAffineOriginFirstOrder318

open OriginalAffineOriginCotangent318
open scoped RightActions

variable {R S B : Type*} [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B]
variable (e : B →ₐ[R] R)

section
variable {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Literal square-zero test algebra over a possibly changed scalar ring.
It retains the fixed origin through the composite ε followed by R→S. -/
abbrev Lift :=
  {f : B →ₐ[R] TrivSqZeroExt S M //
    (TrivSqZeroExt.fstHom R S M).comp f = (Algebra.ofId R S).comp e}

/-- The two coordinates of the genuine lift are ε followed by the scalar
map, and the given relative based derivative. -/
def liftOfDerivation (d : BasedDerivation e M) : Lift (S := S) (M := M) e :=
  ⟨{ toFun := fun b => (algebraMap R S (e b), d.linear b)
     map_one' := by
       apply TrivSqZeroExt.ext
       · simp
       · change d.linear 1 = 0
         simpa using d.base_zero 1
     map_zero' := by
       apply TrivSqZeroExt.ext <;> simp
     map_add' a b := by
       apply TrivSqZeroExt.ext <;> simp
     map_mul' a b := by
       apply TrivSqZeroExt.ext
       · simp
       · simpa only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mk,
           op_smul_eq_smul, algebraMap_smul] using d.leibniz a b
     commutes' r := by
       apply TrivSqZeroExt.ext
       · change algebraMap R S (e (algebraMap R B r)) = algebraMap R S r
         rw [e.commutes]
       · exact d.base_zero r },
   by ext b; rfl⟩

def derivationOfLift (q : Lift (S := S) (M := M) e) : BasedDerivation e M where
  linear := ((TrivSqZeroExt.sndHom S M).restrictScalars R).comp q.1.toLinearMap
  base_zero r := by
    change (q.1 (algebraMap R B r)).snd = 0
    rw [q.1.commutes]
    rfl
  leibniz a b := by
    have h (x : B) : (q.1 x).fst = algebraMap R S (e x) :=
      congrArg (fun k : B →ₐ[R] S => k x) q.2
    change (q.1 (a * b)).snd = e a • (q.1 b).snd + e b • (q.1 a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, h, h, op_smul_eq_smul, algebraMap_smul, algebraMap_smul]

/-- R-linear maps from the actual conormal classify square-zero lifts,
even if S is not flat or has nilpotents. -/
def points : (Cot e →ₗ[R] M) ≃ Lift (S := S) (M := M) e :=
  (universalEquiv e).trans {
    toFun := liftOfDerivation e
    invFun := derivationOfLift e
    left_inv d := by
      cases d
      rfl
    right_inv q := by
      apply Subtype.ext
      apply AlgHom.ext
      intro b
      apply TrivSqZeroExt.ext
      · exact (congrArg (fun k : B →ₐ[R] S => k b) q.2).symm
      · rfl }

theorem points_snd (v : Cot e →ₗ[R] M) (b : B) :
    ((points (S := S) e v).1 b).snd = v (differential e b) := rfl

theorem points_symm_differential (q : Lift (S := S) (M := M) e) (b : B) :
    (points (S := S) e).symm q (differential e b) = (q.1 b).snd :=
  universal_differential e (derivationOfLift e q) b

end

end OriginalAffineOriginFirstOrder318

#print axioms OriginalAffineOriginFirstOrder318.points
#print axioms OriginalAffineOriginFirstOrder318.points_symm_differential
