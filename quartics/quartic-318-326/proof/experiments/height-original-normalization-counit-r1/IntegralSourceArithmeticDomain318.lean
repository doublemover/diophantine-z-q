module
public import IntegralSourceBranches318
public import ContactKummerOrder318
public import Mathlib.Algebra.Polynomial.AlgebraMap
public section
noncomputable section
namespace IntegralSourceArithmeticDomain318
open Polynomial IntegralSourceBranches318
open scoped TensorProduct
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R] [Algebra R ℚ]

/-- The actual coefficient map into the original rational polynomial ring. -/
@[expose] def polynomialMap : R[X] →+* ℚ[X] :=
  Polynomial.mapRingHom (algebraMap R ℚ)
local instance polynomialAlgebra : Algebra R[X] ℚ[X] := (polynomialMap R).toAlgebra
variable (c : Fin 4 → Rˣ)
@[expose] def rationalTwists : Fin 4 → ℚˣ :=
  fun i => Units.map (algebraMap R ℚ).toMonoidHom (c i)

theorem contacts_map (i : Fin 4) :
    algebraMap R ℚ (contacts R i) = LinearContactSquareclass318.contacts i := by
  fin_cases i <;> norm_num [contacts,LinearContactSquareclass318.contacts]

theorem coefficient_map (i : Fin 4) :
    algebraMap R[X] ℚ[X] (coefficient R c i) =
      ContactKummerOrder318.coefficient (rationalTwists R c) i := by
  change Polynomial.map (algebraMap R ℚ)
    (C (c i : R)*(X-C (contacts R i))) = _
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_C,Polynomial.map_X,contacts_map]
  rfl

@[expose] def presentationEquiv {a b : Fin 4 → ℚ[X]} (h : a=b) :
    FourRootOrder318.Order a ≃ₐ[ℚ[X]] FourRootOrder318.Order b := by
  subst b
  exact AlgEquiv.refl

/-- Base change uses all four actual monic quadratic presentations. No
choice of a component, square root or rational point enters this map. -/
@[expose] def rationalBaseChange :
    ℚ[X] ⊗[R[X]] SourceOrder R c ≃ₐ[ℚ[X]]
      ContactKummerOrder318.SourceOrder (rationalTwists R c) :=
  (FourRootOrder318.baseChange (coefficient R c) ℚ[X]).trans
    (presentationEquiv (funext (coefficient_map R c)))

@[expose] def toRational : SourceOrder R c →+*
    ContactKummerOrder318.SourceOrder (rationalTwists R c) :=
  (rationalBaseChange R c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : SourceOrder R c →ₐ[R[X]]
      ℚ[X] ⊗[R[X]] SourceOrder R c).toRingHom

/-- The original integral order embeds into the original rational order
for every actual injective arithmetic coefficient map R→Q. -/
theorem toRational_injective (hR : Function.Injective (algebraMap R ℚ)) :
    Function.Injective (toRational R c) := by
  letI : Module.Free R[X] (SourceOrder R c) :=
    (FourRootOrder318.finite_free (coefficient R c)).2
  have hi : Function.Injective (algebraMap R[X] ℚ[X]) :=
    Polynomial.map_injective hR
  exact (rationalBaseChange R c).injective.comp
    (Algebra.TensorProduct.includeRight_injective (R := R[X]) (A := ℚ[X])
      (B := SourceOrder R c) hi)

/-- Domain structure of the whole original arithmetic source, derived from
its genuine rational embedding rather than supplied as a component premise. -/
theorem source_domain (hR : Function.Injective (algebraMap R ℚ)) :
    IsDomain (SourceOrder R c) := by
  letI := ContactKummerOrder318.source_domain (rationalTwists R c)
  exact Function.Injective.isDomain (toRational R c) (toRational_injective R c hR)

/-- Fraction-ring arithmetic bases provide the injection automatically. -/
theorem source_domain_of_fraction [IsDomain R] [IsFractionRing R ℚ] :
    IsDomain (SourceOrder R c) :=
  source_domain R c (IsFractionRing.injective R ℚ)
end IntegralSourceArithmeticDomain318
