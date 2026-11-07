module
public import WeierstrassChord318
public section
noncomputable section
namespace TorusChord318
open PeriodEisenstein318 LatticeInvariants318 ModularWeierstrass318 LatticeModelPoint318
open ChordAlgebra318 ChordFlow318
set_option maxHeartbeats 0

lemma normalized_slope (k a b x y : ℂ) (hk : k≠0) (hx : x-a≠0) :
    (b/(2*k^3)-y/(2*k^3))/(a/k^2-x/k^2)=ChordAlgebra318.slope a b x y/(2*k) := by
  have hax : a-x≠0 := sub_ne_zero.mpr (sub_ne_zero.mp hx).symm
  unfold ChordAlgebra318.slope
  field_simp
  ring

/-- Ordinary addition of the actual normalized elliptic points follows from the actual ℘ chord formula. -/
theorem point_add_chord (tau : UpperHalfPlane) (z w : ℂ)
    (hz : z ∉ (periods tau).lattice) (hw : w ∉ (periods tau).lattice)
    (hx : (periods tau).weierstrassP z-(periods tau).weierstrassP w≠0)
    (hb : (periods tau).derivWeierstrassP w≠0) :
    point tau (z+w)=point tau z+point tau w := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : 2*(Real.pi:ℂ)≠0 := mul_ne_zero (by norm_num) hp
  have hxn : xCoord tau w≠xCoord tau z := by
    intro he
    have he' := (div_left_inj' (pow_ne_zero 2 hk)).mp he
    exact hx (sub_eq_zero.mpr he'.symm)
  obtain ⟨hR,hY⟩ := WeierstrassChord318.chord_pair (periods tau) z w hz hw hx hb
  rw [point_of_notMem tau (z+w) (WeierstrassChord318.sum_not_mem _ _ _ hx),
    point_of_notMem tau z hz,point_of_notMem tau w hw]
  rw [add_comm (affinePoint tau z hz) (affinePoint tau w hw)]
  unfold affinePoint
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxn,
    WeierstrassCurve.Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_X_ne hxn]
  unfold xCoord yCoord
  rw [normalized_slope (2*(Real.pi:ℂ)) _ _ _ _ hk hx]
  simp only [WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY,WeierstrassCurve.Affine.negAddY,
    curve,NormalizedWeierstrass318.model,zero_mul,sub_zero]
  rw [←hR,←hY]
  simp only [R,Y,chordY,chordX]
  constructor <;> field_simp <;> ring
end TorusChord318
