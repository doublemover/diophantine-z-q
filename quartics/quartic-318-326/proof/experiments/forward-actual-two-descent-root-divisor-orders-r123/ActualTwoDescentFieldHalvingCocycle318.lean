module
public import ActualTwoDescentFieldGaloisTwoTorsion318
public section
noncomputable section
namespace ActualTwoDescentFieldHalvingCocycle318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318
local instance : DecidableEq Qbar := Classical.decEq _

def halfDifference (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) (σ : GalQ) :=
  galoisPointHom σ n hn Q-Q

lemma actual_half_difference_cocycle (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) (σ τ : GalQ) :
    halfDifference n hn Q (σ*τ)=galoisPointHom σ n hn (halfDifference n hn Q τ)+halfDifference n hn Q σ := by
  simp only [halfDifference,actual_galois_mul,map_sub]
  abel

lemma actual_half_difference_torsion (n : F) (hn : n ≠ 0) (P : Point n)
    (Q : Point (algebraMap F Qbar n)) (hQ : Q+Q=rationalPointMap n hn P) (σ : GalQ) :
    halfDifference n hn Q σ+halfDifference n hn Q σ=0 := by
  have he : galoisPointHom σ n hn Q+galoisPointHom σ n hn Q=Q+Q := by
    rw [←map_add,hQ,actual_rational_point_fixed]
  dsimp [halfDifference]
  calc
    _=(galoisPointHom σ n hn Q+galoisPointHom σ n hn Q)-(Q+Q) := by abel
    _=0 := sub_eq_zero.mpr he

/-- The actual half-point difference is a homomorphism because ALL actual two-torsion is rational. -/
def halfCocycle (n : F) (hn : n ≠ 0) (P : Point n)
    (Q : Point (algebraMap F Qbar n)) (hQ : Q+Q=rationalPointMap n hn P) :
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

end ActualTwoDescentFieldHalvingCocycle318
