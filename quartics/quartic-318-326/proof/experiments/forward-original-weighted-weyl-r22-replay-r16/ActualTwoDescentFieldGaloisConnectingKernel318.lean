module
public import ActualTwoDescentFieldGaloisConnectingHom318
public section
noncomputable section
namespace ActualTwoDescentFieldGaloisConnectingKernel318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisConnectingHom318
open ActualTwoDescentActualEllipticFieldMap318
local instance : DecidableEq Qbar := Classical.decEq _

/-- Exact kernel over the base field, using actual infinite Galois fixed-field descent, not a local-to-global assumption. -/
theorem actual_galois_connecting_kernel (n : F) (hn : n ≠ 0) (P : Point n) :
    rationalHalvingCocycle n hn P=1 ↔ ∃ R : Point n, R+R=P := by
  constructor
  · intro H
    let Q := actualHalf n hn (rationalPointMap n hn P)
    have hQ : Q+Q=rationalPointMap n hn P := actual_half_spec n hn _
    have hfixed (σ : GalQ) : galoisPointHom σ n hn Q=Q := by
      apply sub_eq_zero.mp
      have he := congrArg (fun f : GalQ →* Multiplicative (closedTwoTorsion n) => ((f σ).toAdd : Point (algebraMap F Qbar n))) H
      change halfDifference n hn Q σ=0 at he
      exact he
    obtain ⟨R,hR⟩ := actual_fixed_point_rational n hn Q hfixed
    refine ⟨R,?_⟩
    apply actual_elliptic_field_map_injective (algebraMap F Qbar) n hn
    change rationalPointMap n hn (R+R)=rationalPointMap n hn P
    rw [map_add,hR,hQ]
  · rintro ⟨R,rfl⟩
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    change ((rationalHalvingCocycle n hn (R+R) σ).toAdd : Point _)=0
    rw [actual_halving_cocycle_evaluate n hn (R+R) (rationalPointMap n hn R) (by rw [map_add])]
    rw [halfDifference,actual_rational_point_fixed,sub_self]

end ActualTwoDescentFieldGaloisConnectingKernel318
