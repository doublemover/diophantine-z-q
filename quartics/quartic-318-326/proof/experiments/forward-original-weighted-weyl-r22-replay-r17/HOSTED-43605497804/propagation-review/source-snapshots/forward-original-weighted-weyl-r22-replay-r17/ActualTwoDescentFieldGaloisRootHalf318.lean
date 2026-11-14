module
public import ActualTwoDescentFieldTorsionSignEquivalence318
public section
noncomputable section
namespace ActualTwoDescentFieldGaloisRootHalf318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldHalfFlipTranslations318
open ActualTwoDescentHalvingCoordinates318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_galois_root_square (σ : GalQ) (x : F) (a : Qbar) (ha : a^2=algebraMap F Qbar x) :
    (σ a)^2=algebraMap F Qbar x := by rw [←map_pow,ha,σ.commutes]

/-- Exact Galois action on the explicit geometric half-point, retaining the original rational index. -/
lemma actual_galois_root_half (σ : GalQ) (n x : F) (hn : n ≠ 0) (a b c : Qbar)
    (ha : a^2=algebraMap F Qbar x) (hb : b^2=algebraMap F Qbar x-algebraMap F Qbar n)
    (hc : c^2=algebraMap F Qbar x+3*algebraMap F Qbar n) :
    galoisPointHom σ n hn (rootHalf _ _ a b c (rational_parameter_ne n hn) ha hb hc)=
      rootHalf _ _ (σ a) (σ b) (σ c) (rational_parameter_ne n hn)
        (actual_galois_root_square σ x a ha)
        (by simpa only [map_sub] using actual_galois_root_square σ (x-n) b (by simpa only [map_sub] using hb))
        (by simpa only [map_add,map_mul,map_ofNat] using actual_galois_root_square σ (x+3*n) c
          (by simpa only [map_add,map_mul,map_ofNat] using hc)) := by
  simp only [rootHalf,galoisPointHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,galoisPoint,point,
    halfX,halfY,map_add,map_mul,map_neg,σ.commutes]

end ActualTwoDescentFieldGaloisRootHalf318
