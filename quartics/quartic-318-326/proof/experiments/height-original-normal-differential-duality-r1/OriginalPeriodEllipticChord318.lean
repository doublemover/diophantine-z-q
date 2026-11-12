module
public import OriginalPeriodEllipticPoints318
public import WeierstrassChord318
public section
noncomputable section
namespace OriginalPeriodEllipticChord318
open OriginalPeriodWeierstrassCoordinates318 OriginalComplexPeriodPair318
open OriginalPeriodEllipticPoints318 ComplexAffineFreeTranslation318 ChordAlgebra318 ChordFlow318
set_option maxHeartbeats 2800000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
@[expose] def rawPoint (z : ℂ) := point L (projection L z)

lemma projection_nonzero {z : ℂ} (hz : z∉(pair L).lattice) : projection L z≠0 := by
  intro h
  exact hz ((pair_mem L z).mpr ((QuotientAddGroup.eq_zero_iff).mp h))
lemma rawPoint_mem (z : ℂ) (hz : z∈(pair L).lattice) : rawPoint L z=0 := by
  rw [rawPoint,(QuotientAddGroup.eq_zero_iff).mpr ((pair_mem L z).mp hz),point_zero]
lemma rawPoint_period (z : ℂ) (a : (pair L).lattice) : rawPoint L (z+a.val)=rawPoint L z := by
  have ha : projection L a.val=0 :=
    (QuotientAddGroup.eq_zero_iff).mpr ((pair_mem L a.val).mp a.property)
  unfold rawPoint
  change point L ((QuotientAddGroup.mk' L) (z+a.val))=_
  rw [map_add,ha,add_zero]

lemma rawPoint_neg (z : ℂ) : rawPoint L (-z)= -rawPoint L z := by
  by_cases hz : z∈(pair L).lattice
  · rw [rawPoint_mem L z hz,rawPoint_mem L (-z) ((pair L).lattice.neg_mem hz),neg_zero]
  have hn : -z∉(pair L).lattice := fun h => hz (by simpa using (pair L).lattice.neg_mem h)
  rw [rawPoint,rawPoint,point_nonzero L _ (projection_nonzero L hn),
    point_nonzero L _ (projection_nonzero L hz),WeierstrassCurve.Affine.Point.neg_def]
  simp [WeierstrassCurve.Affine.Point.neg,x_projection,y_projection,
    WeierstrassCurve.Affine.negY,curve,NormalizedWeierstrass318.model]

/-- Genuine ordinary chord law on the native algebraic curve carrying
the original sums, from the existing actual Weierstrass chord theorem. -/
theorem rawPoint_add_chord (z w : ℂ) (hz : z∉(pair L).lattice) (hw : w∉(pair L).lattice)
    (hx : (pair L).weierstrassP z-(pair L).weierstrassP w≠0)
    (hb : (pair L).derivWeierstrassP w≠0) :
    rawPoint L (z+w)=rawPoint L z+rawPoint L w := by
  have hxn : x L (projection L w)≠x L (projection L z) := by
    intro he
    exact hx (sub_eq_zero.mpr he.symm)
  obtain ⟨hR,hY⟩ := WeierstrassChord318.chord_pair (pair L) z w hz hw hx hb
  have hs := WeierstrassChord318.sum_not_mem (pair L) z w hx
  rw [rawPoint,rawPoint,rawPoint,point_nonzero L _ (projection_nonzero L hs),
    point_nonzero L _ (projection_nonzero L hz),point_nonzero L _ (projection_nonzero L hw)]
  conv_rhs => rw [add_comm]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxn,
    WeierstrassCurve.Affine.Point.some.injEq,WeierstrassCurve.Affine.slope_of_X_ne hxn]
  simp only [x_projection,y_projection]
  have hax : (pair L).weierstrassP w-(pair L).weierstrassP z≠0 := sub_ne_zero.mpr (sub_ne_zero.mp hx).symm
  have hsl : ((pair L).derivWeierstrassP w/2-(pair L).derivWeierstrassP z/2)/
      ((pair L).weierstrassP w-(pair L).weierstrassP z)=
      ChordAlgebra318.slope ((pair L).weierstrassP w) ((pair L).derivWeierstrassP w)
        ((pair L).weierstrassP z) ((pair L).derivWeierstrassP z)/2 := by
    unfold ChordAlgebra318.slope
    field_simp [hx,hax] <;> ring
  rw [hsl]
  simp only [WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negY,WeierstrassCurve.Affine.negAddY,
    curve,NormalizedWeierstrass318.model,zero_mul,sub_zero]
  rw [←hR,←hY]
  simp only [R,Y,chordY,chordX]
  constructor <;> field_simp <;> ring
end OriginalPeriodEllipticChord318
