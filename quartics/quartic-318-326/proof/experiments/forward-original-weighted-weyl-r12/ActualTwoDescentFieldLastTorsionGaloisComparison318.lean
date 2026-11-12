module
public import ActualTwoDescentFieldLastTorsionRootCharacters318
public section
noncomputable section
namespace ActualTwoDescentFieldLastTorsionGaloisComparison318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentKummerHom318 ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentFieldSquarePairGaloisEquivalence318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldContinuousTorsionCoordinates318
open ActualTwoDescentFieldScalarConnectingHom318 ActualTwoDescentFieldScalarRootCharacters318
open ActualTwoDescentFieldScalarSquareRoots318 ActualTwoDescentFieldHalfFlipTranslations318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldTorsionSignHom318 ActualTwoDescentFieldLastTorsionGeometricHalf318
open ActualTwoDescentFieldLastTorsionRootCharacters318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_last_torsion_galois_comparison (n : F) (hn : n ≠ 0) :
    cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd (torsionPoint n hn)))=
      (squarePairGaloisEquiv (F:=F)) (kummerClass n hn (torsionPoint n hn)) := by
  let u := scalarRoot (Units.mk0 (3 : F) (by norm_num))
  let v := scalarRoot (Units.mk0 (-n) (neg_ne_zero.mpr hn))
  have hu : u^2=3 := by simpa only [Units.val_mk0,map_ofNat] using scalar_root_square (Units.mk0 (3 : F) (by norm_num))
  have hv : v^2= -algebraMap F Qbar n := by
    simpa only [Units.val_mk0,map_neg] using scalar_root_square (Units.mk0 (-n) (neg_ne_zero.mpr hn))
  have hun : u ≠ 0 := scalar_root_ne _
  have hvn : v ≠ 0 := scalar_root_ne _
  let Q := rootHalf _ _ (u*v) (2*v) 0 (rational_parameter_ne n hn)
    (actual_last_half_roots n u v hu hv).1 (actual_last_half_roots n u v hu hv).2.1 (actual_last_half_roots n u v hu hv).2.2
  have hhalf : Q+Q=ActualTwoDescentFieldGaloisFixedRational318.rationalPointMap n hn (torsionPoint n hn) := actual_last_torsion_half n hn u v hu hv
  rw [actual_second_torsion_class]
  change _=(squarePairGaloisEquiv (F:=F)) (ActualTwoDescentSquareClassQuotient318.classOf 3 (by norm_num),
    ActualTwoDescentSquareClassQuotient318.classOf (-n) (neg_ne_zero.mpr hn))
  rw [actual_squarepair_galois_value]
  have hσ (σ : GalQ) : torsionSignHom n hn (rationalHalvingCocycle n hn (torsionPoint n hn) σ)=
      (scalarCharacter (Units.mk0 3 (by norm_num)) σ,scalarCharacter (Units.mk0 (-n) (neg_ne_zero.mpr hn)) σ) := by
    change ActualTwoDescentFieldTorsionSignValues318.torsionSignValue _ _
      ((rationalHalvingCocycle n hn (torsionPoint n hn) σ).toAdd : Point _)=_
    rw [actual_halving_cocycle_evaluate n hn (torsionPoint n hn) Q hhalf]
    exact actual_last_torsion_root_characters σ n hn u v hun hvn hu hv
  apply Prod.ext
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.fst (hσ σ)
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.snd (hσ σ)

end ActualTwoDescentFieldLastTorsionGaloisComparison318
