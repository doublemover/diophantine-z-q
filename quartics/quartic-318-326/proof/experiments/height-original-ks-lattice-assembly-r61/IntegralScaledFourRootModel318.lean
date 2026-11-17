module
public import UnitScaledQuadraticOrder318
public import FourRootOrder318
public section
noncomputable section
namespace IntegralScaledFourRootModel318
open scoped TensorProduct
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Independent scalings of all four roots are actual algebra equivalences
when the scalars are units in the target base. No unit condition is imposed
on their integral representatives in the original base. -/
@[expose] def fourScale (a b : Fin 4 → S) (y : Fin 4 → Sˣ)
    (h : ∀ i, b i = a i * (y i : S)^2) :
    FourRootOrder318.Order b ≃ₐ[S] FourRootOrder318.Order a :=
  Algebra.TensorProduct.congr
    (Algebra.TensorProduct.congr
      (UnitScaledQuadraticOrder318.equiv (a 0) (b 0) (y 0) (h 0))
      (UnitScaledQuadraticOrder318.equiv (a 1) (b 1) (y 1) (h 1)))
    (Algebra.TensorProduct.congr
      (UnitScaledQuadraticOrder318.equiv (a 2) (b 2) (y 2) (h 2))
      (UnitScaledQuadraticOrder318.equiv (a 3) (b 3) (y 3) (h 3)))

/-- Exact generic/base-change comparison for an integral monic four-root
order with cleared coefficients. The only comparison input is the displayed
coefficient equation; no generic-fiber isomorphism is assumed. -/
@[expose] def genericFiber (b : Fin 4 → R) (a : Fin 4 → S) (y : Fin 4 → Sˣ)
    (h : ∀ i, algebraMap R S (b i) = a i * (y i : S)^2) :
    S ⊗[R] FourRootOrder318.Order b ≃ₐ[S] FourRootOrder318.Order a :=
  (FourRootOrder318.baseChange b S).trans
    (fourScale a (fun i => algebraMap R S (b i)) y h)

/-- This integral affine order is finite and free without discriminant,
contact-separation, twist-unit or residue-characteristic assumptions. -/
theorem finite_free (b : Fin 4 → R) :
    Module.Finite R (FourRootOrder318.Order b) ∧
      Module.Free R (FourRootOrder318.Order b) :=
  FourRootOrder318.finite_free b

theorem rank_sixteen [Nontrivial R] (b : Fin 4 → R) :
    Module.finrank R (FourRootOrder318.Order b) = 16 :=
  FourRootOrder318.rank_sixteen b

end IntegralScaledFourRootModel318
