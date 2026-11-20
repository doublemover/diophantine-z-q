module
public import CTOriginalGeometricGaloisAction318
public import Mathlib.Tactic.Abel
public section
noncomputable section
namespace ActualTwoDescentFieldHalvingCocycle318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGaloisPointAction318
local instance : DecidableEq Qbar := Classical.decEq _

def halfDifference (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) (σ : GalQ) :=
  galoisPointHom σ n hn Q-Q

lemma actual_half_difference_cocycle (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) (σ τ : GalQ) :
    halfDifference n hn Q (σ*τ)=galoisPointHom σ n hn (halfDifference n hn Q τ)+halfDifference n hn Q σ := by
  have hmul : galoisPointHom (σ*τ) n hn Q =
      galoisPointHom σ n hn (galoisPointHom τ n hn Q) := by
    let s : Qbar ≃ₐ[F] Qbar := σ
    let t : Qbar ≃ₐ[F] Qbar := τ
    change galoisPointHom (s*t) n hn Q = galoisPointHom s n hn (galoisPointHom t n hn Q)
    exact actual_galois_mul s t n hn Q
  simp only [halfDifference,map_sub]
  rw [hmul]
  abel

end ActualTwoDescentFieldHalvingCocycle318
