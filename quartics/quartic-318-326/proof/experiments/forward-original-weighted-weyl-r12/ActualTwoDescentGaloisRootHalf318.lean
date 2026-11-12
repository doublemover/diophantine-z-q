module
public import ActualTwoDescentTorsionSignEquivalence318
public section
noncomputable section
namespace ActualTwoDescentGaloisRootHalf318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentHalfFlipTranslations318
open ActualTwoDescentHalvingCoordinates318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_galois_root_square (σ : GalQ) (x : ℚ) (a : Qbar) (ha : a^2=algebraMap ℚ Qbar x) :
    (σ a)^2=algebraMap ℚ Qbar x := by rw [←map_pow,ha,σ.commutes]

/-- Exact Galois action on the explicit geometric half-point, retaining the original rational index. -/
lemma actual_galois_root_half (σ : GalQ) (n x : ℚ) (hn : n ≠ 0) (a b c : Qbar)
    (ha : a^2=algebraMap ℚ Qbar x) (hb : b^2=algebraMap ℚ Qbar x-algebraMap ℚ Qbar n)
    (hc : c^2=algebraMap ℚ Qbar x+3*algebraMap ℚ Qbar n) :
    galoisPointHom σ n hn (rootHalf _ _ a b c (rational_parameter_ne n hn) ha hb hc)=
      rootHalf _ _ (σ a) (σ b) (σ c) (rational_parameter_ne n hn)
        (actual_galois_root_square σ x a ha)
        (by simpa only [map_sub] using actual_galois_root_square σ (x-n) b (by simpa only [map_sub] using hb))
        (by simpa only [map_add,map_mul,map_ofNat] using actual_galois_root_square σ (x+3*n) c
          (by simpa only [map_add,map_mul,map_ofNat] using hc)) := by
  simp only [rootHalf,galoisPointHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,galoisPoint,point,
    halfX,halfY,map_add,map_mul,map_neg,σ.commutes]

end ActualTwoDescentGaloisRootHalf318
