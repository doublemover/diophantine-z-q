module
public import ActualTwoDescentHalvingCocycle318
public section
noncomputable section
namespace ActualTwoDescentHalvingChoiceIndependence318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentGaloisFixedRational318
open ActualTwoDescentGaloisTwoTorsion318 ActualTwoDescentHalvingCocycle318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_half_choice_independent (n : ℚ) (hn : n ≠ 0) (P : Point n)
    (Q R : Point (algebraMap ℚ Qbar n)) (hQ : Q+Q=rationalPointMap n hn P)
    (hR : R+R=rationalPointMap n hn P) (σ : GalQ) :
    halfDifference n hn Q σ=halfDifference n hn R σ := by
  have ht : (Q-R)+(Q-R)=0 := by
    calc
      _=(Q+Q)-(R+R) := by abel
      _=0 := by rw [hQ,hR,sub_self]
  have hf := actual_two_torsion_fixed σ n hn (Q-R) ht
  rw [map_sub] at hf
  dsimp [halfDifference]
  calc
    galoisPointHom σ n hn Q-Q=(galoisPointHom σ n hn Q-galoisPointHom σ n hn R)-(Q-R)+(galoisPointHom σ n hn R-R) := by abel
    _=galoisPointHom σ n hn R-R := by rw [hf,sub_self,zero_add]

def rationalHalvingCocycle (n : ℚ) (hn : n ≠ 0) (P : Point n) : GalQ →* Multiplicative (closedTwoTorsion n) :=
  halfCocycle n hn P (actualHalf n hn (rationalPointMap n hn P)) (actual_half_spec n hn _)

lemma actual_halving_cocycle_evaluate (n : ℚ) (hn : n ≠ 0) (P : Point n)
    (Q : Point (algebraMap ℚ Qbar n)) (hQ : Q+Q=rationalPointMap n hn P) (σ : GalQ) :
    ((rationalHalvingCocycle n hn P σ).toAdd : Point (algebraMap ℚ Qbar n))=halfDifference n hn Q σ :=
  actual_half_choice_independent n hn P _ Q (actual_half_spec n hn _) hQ σ

end ActualTwoDescentHalvingChoiceIndependence318
