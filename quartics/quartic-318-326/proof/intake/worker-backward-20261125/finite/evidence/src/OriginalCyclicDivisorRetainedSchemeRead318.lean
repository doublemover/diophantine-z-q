module
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorRetainedSchemeRead318

open AlgebraicGeometry CategoryTheory
open Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} {A : CommRingCat.{u}} {E : Type u} [Field E]
variable (j : Spec A ⟶ X) [IsOpenImmersion j] (r : Spec (CommRingCat.of E) ⟶ X)
variable (inChart : Set.range r ⊆ Set.range j)

/-- The lift of the original retained point itself, not a new point
with the same one coordinate, even when the fibre is disconnected. -/
abbrev lift := IsOpenImmersion.lift j r inChart

abbrev ringRead : A →+* E := (Spec.preimage (lift j r inChart)).hom

theorem same_arrow : Spec.map (CommRingCat.ofHom (ringRead j r inChart)) ≫ j = r := by
  have h : Spec.map (CommRingCat.ofHom (ringRead j r inChart)) = lift j r inChart :=
    Spec.map_preimage _
  exact (congrArg (fun s : Spec (CommRingCat.of E) ⟶ Spec A => s ≫ j) h).trans
    (IsOpenImmersion.lift_fac j r inChart)

variable (f : X ⟶ Spec (CommRingCat.of E)) (section_eq : r ≫ f = 𝟙 _)

section Scalar
variable [Algebra E A]
variable (on_base : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap E A)))

include section_eq on_base in
/-- Algebra-linearity follows from the genuine section identity, not
from a second comparison of field choices. -/
theorem maps_constants (e : E) : ringRead j r inChart (algebraMap E A e)=e := by
  let u : CommRingCat.of E ⟶ A := CommRingCat.ofHom (algebraMap E A)
  let d : A ⟶ CommRingCat.of E := CommRingCat.ofHom (ringRead j r inChart)
  have hs : u ≫ d = 𝟙 (CommRingCat.of E) := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_id]
    calc
      Spec.map d ≫ Spec.map u = Spec.map d ≫ (j ≫ f) :=
        congrArg (fun a : Spec A ⟶ Spec (CommRingCat.of E) => Spec.map d ≫ a) on_base.symm
      _ = (Spec.map d ≫ j) ≫ f := (Category.assoc _ _ _).symm
      _ = r ≫ f :=
        congrArg (fun a : Spec (CommRingCat.of E) ⟶ X => a ≫ f) (same_arrow j r inChart)
      _ = _ := section_eq
  exact congrArg (fun h : CommRingCat.of E ⟶ CommRingCat.of E => h.hom e) hs

def read : A →ₐ[E] E where
  toRingHom := ringRead j r inChart
  commutes' := maps_constants j r inChart f section_eq on_base

theorem read_returns : Spec.map (CommRingCat.ofHom (read j r inChart f section_eq on_base).toRingHom) ≫ j = r :=
  same_arrow j r inChart

section Parameter
variable [Algebra E[X] A]
variable (n : E)

abbrev coord : Spec A ⟶ Spec (CommRingCat.of E[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap E[X] A))

abbrev baseAt : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of E[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval n : E[X] →ₐ[E] E).toRingHom)

variable (literal : lift j r inChart ≫ coord (A:=A) (E:=E) = baseAt n)

include literal in
/-- The actual polynomial coordinate read via the original section.
The full ring read was fixed beforehand by Spec.preimage. -/
theorem parameter_read :
    read j r inChart f section_eq on_base (algebraMap E[X] A Polynomial.X)=n := by
  let u : CommRingCat.of E[X] ⟶ A := CommRingCat.ofHom (algebraMap E[X] A)
  let d : A ⟶ CommRingCat.of E := Spec.preimage (lift j r inChart)
  let b : CommRingCat.of E[X] ⟶ CommRingCat.of E :=
    CommRingCat.ofHom (Polynomial.aeval n : E[X] →ₐ[E] E).toRingHom
  have hs : u ≫ d = b := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    have hr : Spec.map d = lift j r inChart := Spec.map_preimage _
    rw [hr]
    exact literal
  have atX := congrArg (fun h : CommRingCat.of E[X] ⟶ CommRingCat.of E => h.hom Polynomial.X) hs
  exact atX.trans (Polynomial.aeval_X n)

end Parameter
end Scalar
end OriginalCyclicDivisorRetainedSchemeRead318

#print axioms OriginalCyclicDivisorRetainedSchemeRead318.read_returns
#print axioms OriginalCyclicDivisorRetainedSchemeRead318.parameter_read
