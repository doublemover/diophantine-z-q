module
public import IntegralClosureAlongRingMap318
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public section
noncomputable section
namespace IntegralClosureScalarEquiv318
variable {P Q B : Type*} [CommRing P] [CommRing Q] [CommRing B]
  (f : P →+* B) (g : Q →+* B) (e : P ≃+* Q) (he : g.comp e.toRingHom=f)

include he in
lemma integral_iff (z : B) : f.IsIntegralElem z ↔ g.IsIntegralElem z := by
  letI : Algebra P B := f.toAlgebra
  letI : Algebra Q B := g.toAlgebra
  exact e.isIntegral_iff he z

/-- Identity on ambient elements, not an abstract equal-degree equivalence.
The exact native RingEquiv.isIntegral_iff retains both scalar maps. -/
@[expose] def equivalence :
    IntegralClosureAlongRingMap318.Closure f ≃+*
      IntegralClosureAlongRingMap318.Closure g where
  toFun z := ⟨z.val,(integral_iff f g e he z.val).mp z.property⟩
  invFun z := ⟨z.val,(integral_iff f g e he z.val).mpr z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

lemma ambient (z : IntegralClosureAlongRingMap318.Closure f) :
    (equivalence f g e he z : B)=z.val := rfl
end IntegralClosureScalarEquiv318
