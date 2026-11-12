module
public import IntegralRootPointMaps318
public import FourRootDualityBaseChange318
public section
noncomputable section
namespace FourRootRatioOrder318
open FourRootOrderSigns318
variable {R : Type*} [CommRing R] (q : R) (r : Fin 3 → R)

/-- The original order has a common ramified factor in all four equations. -/
@[expose] def original : Fin 4 → R := Fin.cases q (fun i => q*r i)
/-- The ratio order retains the first root and replaces the other three by
its actual ratios. These are honest monic quadratic quotient algebras. -/
@[expose] def normalized : Fin 4 → R := Fin.cases q r
abbrev OriginalOrder := FourRootOrder318.Order (original q r)
abbrev RatioOrder := FourRootOrder318.Order (normalized q r)
@[expose] def marked : Fin 4 → RatioOrder q r :=
  Fin.cases (generator (normalized q r) 0)
    (fun i => generator (normalized q r) 0 * generator (normalized q r) i.succ)

lemma marked_square (i : Fin 4) : (marked q r i)^2 =
    algebraMap R (RatioOrder q r) (original q r i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact generator_square (normalized q r) 0
  · simp only [marked,original,Fin.cases_succ,mul_pow,generator_square,
      normalized,Fin.cases_zero,Fin.cases_succ,map_mul]

/-- Actual map from the ENTIRE original order, retaining every marked
root and the literal base scalar map. It is not a pointwise substitution. -/
@[expose] def map : OriginalOrder q r →ₐ[R] RatioOrder q r :=
  IntegralRootPointMaps318.fourMap (original q r) (marked q r) (marked_square q r)
lemma map_root (i : Fin 4) : map q r (generator (original q r) i) = marked q r i :=
  IntegralRootPointMaps318.fourMap_generator _ _ _ i
lemma map_scalar (x : R) : map q r (algebraMap R (OriginalOrder q r) x) =
    algebraMap R (RatioOrder q r) x := (map q r).commutes x

/-- The ratio extension is finite over the ACTUAL original order: its
whole rank16 base-module generators remain generators over that order. -/
lemma finite : letI : Algebra (OriginalOrder q r) (RatioOrder q r) := (map q r).toRingHom.toAlgebra
    Module.Finite (OriginalOrder q r) (RatioOrder q r) := by
  letI : Algebra (OriginalOrder q r) (RatioOrder q r) := (map q r).toRingHom.toAlgebra
  letI : IsScalarTower R (OriginalOrder q r) (RatioOrder q r) :=
    IsScalarTower.of_algebraMap_eq (fun x => (map_scalar q r x).symm)
  haveI : Module.Finite R (RatioOrder q r) := (FourRootOrder318.finite_free (normalized q r)).1
  exact Module.Finite.of_restrictScalars_finite R (OriginalOrder q r) (RatioOrder q r)
end FourRootRatioOrder318
