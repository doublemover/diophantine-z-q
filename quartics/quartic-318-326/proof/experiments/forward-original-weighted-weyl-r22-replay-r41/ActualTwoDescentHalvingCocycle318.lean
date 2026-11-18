module
public import ActualTwoDescentGaloisTwoTorsion318
public section
noncomputable section
namespace ActualTwoDescentHalvingCocycle318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentGaloisFixedRational318
open ActualTwoDescentGaloisTwoTorsion318
local instance : DecidableEq Qbar := Classical.decEq _

def halfDifference (n : ℚ) (hn : n ≠ 0) (Q : Point (algebraMap ℚ Qbar n)) (σ : GalQ) :=
  galoisPointHom σ n hn Q-Q

lemma actual_half_difference_cocycle (n : ℚ) (hn : n ≠ 0) (Q : Point (algebraMap ℚ Qbar n)) (σ τ : GalQ) :
    halfDifference n hn Q (σ*τ)=galoisPointHom σ n hn (halfDifference n hn Q τ)+halfDifference n hn Q σ := by
  simp only [halfDifference,actual_galois_mul,map_sub]
  abel

lemma actual_half_difference_torsion (n : ℚ) (hn : n ≠ 0) (P : Point n)
    (Q : Point (algebraMap ℚ Qbar n)) (hQ : Q+Q=rationalPointMap n hn P) (σ : GalQ) :
    halfDifference n hn Q σ+halfDifference n hn Q σ=0 := by
  have he : galoisPointHom σ n hn Q+galoisPointHom σ n hn Q=Q+Q := by
    rw [←map_add,hQ,actual_rational_point_fixed]
  dsimp [halfDifference]
  calc
    _=(galoisPointHom σ n hn Q+galoisPointHom σ n hn Q)-(Q+Q) := by abel
    _=0 := sub_eq_zero.mpr he

/-- The actual half-point difference is a homomorphism because ALL actual two-torsion is rational. -/
def halfCocycle (n : ℚ) (hn : n ≠ 0) (P : Point n)
    (Q : Point (algebraMap ℚ Qbar n)) (hQ : Q+Q=rationalPointMap n hn P) :
    GalQ →* Multiplicative (closedTwoTorsion n) where
  toFun σ := Multiplicative.ofAdd ⟨halfDifference n hn Q σ,by
    simpa only [AddMonoidHom.mem_ker,nsmulAddMonoidHom_apply,two_nsmul] using actual_half_difference_torsion n hn P Q hQ σ⟩
  map_one' := by
    apply Subtype.ext
    change halfDifference n hn Q 1=0
    rw [halfDifference,actual_galois_one,sub_self]
  map_mul' σ τ := by
    apply Subtype.ext
    change halfDifference n hn Q (σ*τ)=halfDifference n hn Q σ+halfDifference n hn Q τ
    rw [actual_half_difference_cocycle,
      actual_two_torsion_fixed σ n hn _ (actual_half_difference_torsion n hn P Q hQ τ)]
    exact add_comm _ _

end ActualTwoDescentHalvingCocycle318
