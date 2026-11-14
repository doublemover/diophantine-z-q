module
public import ActualTwoDescentGaloisPointAction318
public section
noncomputable section
namespace ActualTwoDescentGaloisFixedRational318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentActualEllipticFieldMap318
open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentGaloisPointAction318
local instance : DecidableEq Qbar := Classical.decEq _

def rationalPointMap (n : ℚ) (hn : n ≠ 0) : Point n →+ Point (algebraMap ℚ Qbar n) :=
  ellipticFieldMap (algebraMap ℚ Qbar) n hn

lemma actual_rational_point_fixed (σ : GalQ) (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    galoisPointHom σ n hn (rationalPointMap n hn P)=rationalPointMap n hn P := by
  cases P with
  | zero => rfl
  | some x y h => simp only [rationalPointMap,ellipticFieldMap,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      pointMap,galoisPointHom,galoisPoint,point,σ.commutes]

lemma actual_fixed_coordinate_rational (x : Qbar) (hx : ∀ σ : GalQ, σ x=x) :
    ∃ a : ℚ, algebraMap ℚ Qbar a=x :=
  (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hx

/-- Actual fixed points descend to rational points by descent of BOTH affine coordinates. -/
theorem actual_fixed_point_rational (n : ℚ) (hn : n ≠ 0) (P : Point (algebraMap ℚ Qbar n))
    (hP : ∀ σ : GalQ, galoisPointHom σ n hn P=P) : ∃ R : Point n, rationalPointMap n hn R=P := by
  cases P with
  | zero => exact ⟨0,rfl⟩
  | some x y h =>
    have hxy (σ : GalQ) : σ x=x ∧ σ y=y := by
      simpa only [galoisPointHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,galoisPoint,point,
        WeierstrassCurve.Affine.Point.some.injEq] using hP σ
    obtain ⟨a,ha⟩ := actual_fixed_coordinate_rational x (fun σ => (hxy σ).1)
    obtain ⟨b,hb⟩ := actual_fixed_coordinate_rational y (fun σ => (hxy σ).2)
    have hc : b^2=a*(a-n)*(a+3*n) := by
      apply (algebraMap ℚ Qbar).injective
      simpa only [map_pow,map_mul,map_sub,map_add,map_ofNat,ha,hb] using (curve_equation _ x y).mp h.left
    exact ⟨point n a b hn hc,by simp only [rationalPointMap,ellipticFieldMap,AddMonoidHom.coe_mk,
      ZeroHom.coe_mk,pointMap,point,ha,hb]⟩

end ActualTwoDescentGaloisFixedRational318
