module
public import ActualTwoDescentContinuousCharacterRestriction318
public section
noncomputable section
namespace ActualTwoDescentScalarRestrictionNaturality318
set_option maxHeartbeats 16000000

open ActualTwoDescentClosureFieldEmbedding318 ActualTwoDescentContinuousCharacterRestriction318
open ActualTwoDescentFieldSquareOneUnits318 ActualTwoDescentFieldScalarConnectingHom318
open ActualTwoDescentFieldScalarSquareRoots318 ActualTwoDescentFieldScalarRootCharacters318
open ActualTwoDescentFieldScalarRootIndependence318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]

/-- Canonical scalar root characters commute with the actual chosen closure embedding and actual Galois restriction. -/
theorem actual_scalar_restriction_naturality (f : F →+* L) (a : Fˣ) :
    scalarConnectingHom (F:=L) (Units.map f.toMonoidHom a)=
      characterRestriction f (scalarConnectingHom (F:=F) a) := by
  let r := scalarRoot a
  have hr : r ≠ 0 := scalar_root_ne a
  have hjr : closureMap f r ≠ 0 := ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero (closureMap f) hr
  have hsq : (closureMap f r)^2=algebraMap L (AlgebraicClosure L) ((Units.map f.toMonoidHom a : Lˣ) : L) := by
    rw [←map_pow,scalar_root_square,actual_closure_map_base]
    rfl
  apply Subtype.ext; apply MonoidHom.ext; intro σ
  apply Subtype.ext; apply Units.ext
  change ((scalarCharacter (Units.map f.toMonoidHom a) σ : (AlgebraicClosure L)ˣ) : AlgebraicClosure L)=
    closureMap f (((scalarCharacter a (Field.absoluteGaloisGroup.map f σ) : (AlgebraicClosure F)ˣ) : AlgebraicClosure F))
  rw [actual_scalar_character_evaluate _ (closureMap f r) hjr hsq σ,
    actual_scalar_character_evaluate a r hr (scalar_root_square a) (Field.absoluteGaloisGroup.map f σ),
    map_div,actual_closure_map_galois]

end ActualTwoDescentScalarRestrictionNaturality318
