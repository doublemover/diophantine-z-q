module
public import ActualTwoDescentScalarRestrictionNaturality318
public section
noncomputable section
namespace ActualTwoDescentSquareclassRestrictionNaturality318
set_option maxHeartbeats 16000000

open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentSquareClassFieldMap318
open ActualTwoDescentFieldScalarGaloisEquivalence318 ActualTwoDescentFieldSquarePairGaloisEquivalence318
open ActualTwoDescentFieldScalarConnectingHom318 ActualTwoDescentContinuousCharacterRestriction318
open ActualTwoDescentScalarRestrictionNaturality318
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]

lemma actual_scalar_equiv_restriction (f : F →+* L) (z : SquareClass F) :
    scalarGaloisEquiv (F:=L) (squareClassMap f z)=characterRestriction f (scalarGaloisEquiv (F:=F) z) := by
  refine QuotientGroup.induction_on z ?_
  intro a
  have he : (QuotientGroup.mk a : SquareClass F)=classOf (a : F) a.ne_zero := by
    congr 1
    apply Units.ext
    rfl
  rw [he,actual_squareclass_map_value,actual_scalar_galois_value,actual_scalar_galois_value]
  have hu : Units.mk0 (f (a : F)) (field_map_ne_zero f a.ne_zero)=Units.map f.toMonoidHom a := by
    apply Units.ext; rfl
  have ha : Units.mk0 (a : F) a.ne_zero=a := by apply Units.ext; rfl
  rw [hu,ha]
  exact actual_scalar_restriction_naturality f a

theorem actual_pair_equiv_restriction (f : F →+* L) (z : SquareClass F × SquareClass F) :
    squarePairGaloisEquiv (F:=L) (squarePairMap f z)=
      pairCharacterRestriction f (squarePairGaloisEquiv (F:=F) z) := by
  apply Prod.ext
  · exact actual_scalar_equiv_restriction f z.1
  · exact actual_scalar_equiv_restriction f z.2

end ActualTwoDescentSquareclassRestrictionNaturality318
