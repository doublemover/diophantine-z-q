module
public import ActualTwoDescentFullPrimarySelmerPruefer318
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Module.ZMod
public section
noncomputable section
namespace ActualTwoDescentCyclicEndCoordinates318
set_option maxHeartbeats 16000000

variable {m : ℕ} [NeZero m] {A : Type} [AddCommGroup A]

/-- Scalar coordinate of an ACTUAL endomorphism relative to an actual cyclic equivalence. -/
def cyclicEndCoordinate (e : ZMod m ≃+ A) (f : AddMonoid.End A) : ZMod m :=
  e.symm (f (e 1))

lemma actual_zmod_additive_scalar (f : ZMod m →+ ZMod m) (z : ZMod m) :
    f z=z*f 1 := by
  simpa only [nsmul_eq_mul,mul_one,ZMod.natCast_zmod_val] using map_nsmul f (1 : ZMod m) z.val

lemma actual_cyclic_end_coordinate (e : ZMod m ≃+ A) (f : AddMonoid.End A) (x : A) :
    e.symm (f x)=cyclicEndCoordinate e f*e.symm x := by
  have h := actual_zmod_additive_scalar
    (e.symm.toAddMonoidHom.comp (f.comp e.toAddMonoidHom)) (e.symm x)
  simpa only [AddMonoidHom.comp_apply,AddEquiv.coe_toAddMonoidHom,
    e.apply_symm_apply,cyclicEndCoordinate,mul_comm] using h

lemma actual_cyclic_end_scalar (e : ZMod m ≃+ A) (f : AddMonoid.End A) (x : A) :
    f x=(cyclicEndCoordinate e f).val • x := by
  apply e.symm.injective
  rw [actual_cyclic_end_coordinate,map_nsmul]
  simp only [nsmul_eq_mul,ZMod.natCast_zmod_val]

/-- Composition gives multiplication of the SAME actual cyclic scalar. -/
def cyclicEndCoordinateHom (e : ZMod m ≃+ A) : AddMonoid.End A →+* ZMod m where
  toFun := cyclicEndCoordinate e
  map_zero' := by simp [cyclicEndCoordinate]
  map_one' := by simp [cyclicEndCoordinate]
  map_add' f g := by simp [cyclicEndCoordinate,map_add]
  map_mul' f g := by
    change e.symm (f (g (e 1)))=cyclicEndCoordinate e f*cyclicEndCoordinate e g
    rw [actual_cyclic_end_coordinate]
    rfl

lemma actual_cyclic_end_coordinate_injective (e : ZMod m ≃+ A) :
    Function.Injective (cyclicEndCoordinateHom e) := by
  intro f g h
  ext x
  apply e.symm.injective
  rw [actual_cyclic_end_coordinate,actual_cyclic_end_coordinate]
  exact congrArg (fun z : ZMod m => z*e.symm x) h

end ActualTwoDescentCyclicEndCoordinates318
