module
public import ActualTwoDescentFieldScalarRootIndependence318
public section
noncomputable section
namespace ActualTwoDescentFieldScalarConnectingHom318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentFieldScalarSquareRoots318 ActualTwoDescentFieldScalarRootCharacters318
open ActualTwoDescentFieldScalarRootIndependence318

def continuousCharacters : Subgroup (GalQ →* SquareOne Qbar) where
  carrier := {χ | IsLocallyConstant χ}
  one_mem' := IsLocallyConstant.const 1
  mul_mem' hf hg := hf.mul hg
  inv_mem' hf := hf.inv

def scalarConnectingHom : Fˣ →* (continuousCharacters (F:=F)) where
  toFun a := ⟨scalarCharacter a,actual_root_character_locally_constant a _ (scalar_root_ne a) (scalar_root_square a)⟩
  map_one' := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    apply Units.ext
    rw [actual_scalar_character_evaluate 1 1 one_ne_zero (by simp)]
    simp only [map_one,div_one]
    rfl
  map_mul' a b := Subtype.ext (actual_scalar_character_mul a b)

end ActualTwoDescentFieldScalarConnectingHom318
