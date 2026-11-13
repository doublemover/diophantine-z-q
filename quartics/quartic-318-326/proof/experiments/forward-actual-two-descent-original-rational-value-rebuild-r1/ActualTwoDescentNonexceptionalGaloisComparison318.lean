module
public import ActualTwoDescentNonexceptionalRootCharacters318
public section
noncomputable section
namespace ActualTwoDescentNonexceptionalGaloisComparison318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentKummerHom318 ActualTwoDescentKummerAffineCoordinates318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentSquarePairGaloisEquivalence318
open ActualTwoDescentScalarConnectingHom318 ActualTwoDescentScalarRootCharacters318
open ActualTwoDescentContinuousGaloisCocycles318 ActualTwoDescentContinuousTorsionCoordinates318
open ActualTwoDescentGaloisFixedRational318 ActualTwoDescentHalvingChoiceIndependence318
open ActualTwoDescentNonexceptionalGeometricRoots318 ActualTwoDescentNonexceptionalRootCharacters318
open ActualTwoDescentHalfFlipTranslations318 ActualTwoDescentHalvingGroup318
open ActualTwoDescentTorsionSignHom318 ActualTwoDescentGaloisTwoTorsion318
local instance : DecidableEq Qbar := Classical.decEq _

/-- Actual elliptic Kummer/Galois compatibility for every original nonexceptional rational point. -/
theorem actual_nonexceptional_galois_comparison (n x y : ℚ) (hn : n ≠ 0)
    (hx : x ≠ 0) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0) (hc : y^2=x*(x-n)*(x+3*n)) :
    cocyclePair n hn (continuousConnectingHom n hn (Multiplicative.ofAdd (point n x y hn hc)))=
      squarePairGaloisEquiv (kummerClass n hn (point n x y hn hc)) := by
  obtain ⟨a,b,c,han,hbn,hcn,ha,hb,hcc,hp⟩ := actual_nonexceptional_geometric_roots n x y hx hB hA hc
  let Q := rootHalf _ _ a b c (rational_parameter_ne n hn) ha hb hcc
  have hhalf : Q+Q=rationalPointMap n hn (point n x y hn hc) :=
    actual_half_add_self _ _ _ a b c (rational_parameter_ne n hn)
      (ActualTwoDescentEllipticFieldCoordinates318.actual_curve_equation_map (algebraMap ℚ Qbar) n x y hc) ha hb hcc hp
  have hK : kummerClass n hn (point n x y hn hc)=(classOf (x+3*n) hA,classOf (x-n) hB) := by
    apply Prod.ext
    · change classOf (ActualTwoDescentSimpleRootCoordinates318.rootCoordinate (ActualTwoDescentSimpleRootCoordinates318.firstRoot n hn) _) _=_
      rw [actual_first_coordinate n x y hn _ hA]
    · change classOf (ActualTwoDescentSimpleRootCoordinates318.rootCoordinate (ActualTwoDescentSimpleRootCoordinates318.secondRoot n hn) _) _=_
      rw [actual_second_coordinate n x y hn _ hB]
  rw [hK,actual_squarepair_galois_value]
  have hσ (σ : GalQ) : torsionSignHom n hn (rationalHalvingCocycle n hn (point n x y hn hc) σ)=
      (scalarCharacter (Units.mk0 (x+3*n) hA) σ,scalarCharacter (Units.mk0 (x-n) hB) σ) := by
    change ActualTwoDescentTorsionSignValues318.torsionSignValue _ _
      ((rationalHalvingCocycle n hn (point n x y hn hc) σ).toAdd : Point _)=_
    rw [actual_halving_cocycle_evaluate n hn (point n x y hn hc) Q hhalf]
    exact actual_nonexceptional_root_character_pair σ n x y hn hB hA a b c han hbn hcn ha hb hcc hp
  apply Prod.ext
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.fst (hσ σ)
  · apply Subtype.ext; apply MonoidHom.ext; intro σ
    exact congrArg Prod.snd (hσ σ)

end ActualTwoDescentNonexceptionalGaloisComparison318
