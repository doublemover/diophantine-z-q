module
public import FiniteDualModuleAction318
public section
noncomputable section
namespace FiniteDualRestriction318
open FiniteDualModuleAction318
variable {P A N : Type*} [CommRing P] [CommRing A] [CommRing N]
  [Algebra P A] [Algebra P N] (i : A →ₐ[P] N)

/-- Restriction along the ACTUAL order map, with the domain action
restricted along that same map. No chosen frame enters this counit. -/
@[expose] def restriction :
    letI : Module A (Dual P N) := Module.compHom _ i.toRingHom
    Dual P N →ₗ[A] Dual P A := by
  letI : Module A (Dual P N) := Module.compHom _ i.toRingHom
  exact
    { toFun := fun f => f.comp i.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun a f => by
        apply LinearMap.ext
        intro x
        change f (i a*i x)=f (i (a*x))
        rw [map_mul] }

lemma restriction_apply (f : Dual P N) (x : A) :
    evaluate P A (restriction i f) x=evaluate P N f (i x) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (F : TensorCoefficientDuality318.Frame P A ι)

/-- Coordinate in the genuine raw finite-dual frame of the whole
restriction functional, not just its value at one element. -/
@[expose] def coordinate :
    letI : Module A (Dual P N) := Module.compHom _ i.toRingHom
    Dual P N →ₗ[A] A := by
  letI : Module A (Dual P N) := Module.compHom _ i.toRingHom
  exact (frame P A F).symm.toLinearMap.comp (restriction i)

lemma frame_coordinate (f : Dual P N) :
    frame P A F (coordinate i F f)=restriction i f :=
  (frame P A F).apply_symm_apply _

lemma coordinate_value (f : Dual P N) (x : A) :
    F.coefficient (coordinate i F f*x)=f (i x) :=
  congrArg (fun g : Dual P A => evaluate P A g x) (frame_coordinate i F f)
end FiniteDualRestriction318
