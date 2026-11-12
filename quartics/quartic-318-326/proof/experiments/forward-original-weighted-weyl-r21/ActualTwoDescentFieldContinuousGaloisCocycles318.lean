module
public import ActualTwoDescentFieldGaloisLocallyConstant318
public section
noncomputable section
namespace ActualTwoDescentFieldContinuousGaloisCocycles318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingChoiceIndependence318
open ActualTwoDescentFieldGaloisConnectingHom318 ActualTwoDescentFieldGaloisLocallyConstant318
local instance : DecidableEq Qbar := Classical.decEq _

/-- Actual locally constant homomorphisms for the trivial action on the full rational E[2]. -/
def continuousCocycles (n : F) : Subgroup (GalQ →* Multiplicative (closedTwoTorsion n)) where
  carrier := {f | IsLocallyConstant f}
  one_mem' := IsLocallyConstant.const 1
  mul_mem' hf hg := hf.mul hg
  inv_mem' hf := hf.inv

def continuousConnectingHom (n : F) (hn : n ≠ 0) : Multiplicative (Point n) →* continuousCocycles n where
  toFun P := ⟨galoisConnectingHom n hn P,actual_halving_cocycle_locally_constant n hn P.toAdd⟩
  map_one' := Subtype.ext ((galoisConnectingHom n hn).map_one)
  map_mul' P Q := Subtype.ext ((galoisConnectingHom n hn).map_mul P Q)

lemma actual_continuous_connecting_kernel (n : F) (hn : n ≠ 0) :
    (continuousConnectingHom n hn).ker=(powMonoidHom (α:=Multiplicative (Point n)) 2).range := by
  ext P
  change continuousConnectingHom n hn P=1 ↔ ∃ Q : Multiplicative (Point n), Q^2=P
  rw [Subtype.ext_iff]
  change rationalHalvingCocycle n hn P.toAdd=1 ↔ _
  rw [ActualTwoDescentFieldGaloisConnectingKernel318.actual_galois_connecting_kernel]
  constructor
  · rintro ⟨Q,hQ⟩
    exact ⟨Multiplicative.ofAdd Q,by rw [pow_two]; exact congrArg Multiplicative.ofAdd hQ⟩
  · rintro ⟨Q,hQ⟩
    refine ⟨Q.toAdd,?_⟩
    rw [pow_two] at hQ
    exact congrArg Multiplicative.toAdd hQ

end ActualTwoDescentFieldContinuousGaloisCocycles318
