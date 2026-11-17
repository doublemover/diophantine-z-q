module
public import ActualTwoDescentCyclicEndCoordinates318
public section
noncomputable section
namespace ActualTwoDescentAdditivePrimaryLevels318
set_option maxHeartbeats 16000000
open ActualTwoDescentPrimaryPowerLevels318
variable (A : Type) [AddCommGroup A]

abbrev additivePowerLevel (k : ℕ) : AddSubgroup A := (nsmulAddMonoidHom A (2^k)).ker

def additivePowerLevelEquiv (k : ℕ) :
    additivePowerLevel A k ≃+ Additive (powerLevel (Multiplicative A) k) where
  toFun x := Additive.ofMul ⟨Multiplicative.ofAdd x.val,x.property⟩
  invFun x := ⟨x.toMul.val.toAdd,x.toMul.property⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

def additiveLevelEnd (k : ℕ) (f : AddMonoid.End A) : AddMonoid.End (additivePowerLevel A k) where
  toFun x := ⟨f x.val,by
    change (2^k) • f x.val=0
    rw [←map_nsmul,x.property,map_zero]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.val y.val)

def additiveLevelEndHom (k : ℕ) : AddMonoid.End A →+* AddMonoid.End (additivePowerLevel A k) where
  toFun := additiveLevelEnd A k
  map_zero' := by ext x; rfl
  map_one' := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_mul' f g := by ext x; rfl

end ActualTwoDescentAdditivePrimaryLevels318
