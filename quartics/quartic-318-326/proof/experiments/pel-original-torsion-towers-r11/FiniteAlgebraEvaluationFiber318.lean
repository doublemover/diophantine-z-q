module
public import WholeGeneratorEvaluationSeparation318
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
public section
noncomputable section
namespace FiniteAlgebraEvaluationFiber318
open Set Polynomial
variable {F R A : Type*} [Field F] [CommRing R] [Algebra F R]
  [CommRing A] [Algebra R A] [Algebra F A] [IsScalarTower F R A] [Module.Finite R A]

/-- EVERY exact base fiber of the whole algebra has finitely many
F-valued evaluations. Actual monic integral equations constrain each
whole-ring generator, and full generation gives injection into their
finite root product. No geometric point bijection is assumed. -/
theorem finite {ι : Type*} [Fintype ι] (a : ι → A)
    (hgen : Function.Surjective (MvPolynomial.aeval a : MvPolynomial ι F →ₐ[F] A))
    (v : R →ₐ[F] F) :
    {f : A →ₐ[F] F | ∀ r : R, f (algebraMap R A r) = v r}.Finite := by
  classical
  let V := {f : A →ₐ[F] F // ∀ r : R, f (algebraMap R A r) = v r}
  let P (i : ι) : Polynomial F := (minpoly R (a i)).map v.toRingHom
  let Z (i : ι) := {z : F // (P i).IsRoot z}
  have hm (i : ι) : (P i).Monic := (minpoly.monic (IsIntegral.of_finite R (a i))).map _
  letI (i : ι) : Fintype (Z i) :=
    (Polynomial.finite_setOfPred_isRoot (hm i).ne_zero).fintype
  have hroot (f : V) (i : ι) : (P i).IsRoot (f.val (a i)) := by
    have hs : f.val.toRingHom.comp (algebraMap R A) = v.toRingHom := by
      ext r
      exact f.property r
    have hz := congrArg f.val.toRingHom (minpoly.aeval R (a i))
    simp only [Polynomial.aeval_def,Polynomial.hom_eval₂,hs,map_zero] at hz
    simpa only [P,Polynomial.IsRoot,Polynomial.eval_map] using hz
  let E (f : V) : ∀ i, Z i := fun i => ⟨f.val (a i),hroot f i⟩
  have hE : Function.Injective E := by
    intro f g h
    apply Subtype.ext
    apply WholeGeneratorEvaluationSeparation318.algebra_hom_ext a hgen
    intro i
    exact congrArg Subtype.val (congrFun h i)
  letI : Finite V := Finite.of_injective E hE
  exact Set.toFinite _
end FiniteAlgebraEvaluationFiber318
