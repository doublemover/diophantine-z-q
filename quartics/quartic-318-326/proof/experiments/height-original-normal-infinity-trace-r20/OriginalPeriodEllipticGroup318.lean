module
public import OriginalPeriodEllipticChord318
public import WeierstrassAvoidance318
public section
noncomputable section
namespace OriginalPeriodEllipticGroup318
open OriginalComplexPeriodPair318 OriginalPeriodEllipticPoints318
open OriginalPeriodEllipticChord318 ComplexAffineFreeTranslation318
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- The genuine original point map preserves addition in ALL cases.
Actual auxiliary arguments reduce tangent and two-torsion exceptions to
ordinary chords; the algebraic law is not transported from the torus. -/
theorem rawPoint_add (z w : ℂ) : rawPoint L (z+w)=rawPoint L z+rawPoint L w := by
  by_cases hz : z∈(pair L).lattice
  · rw [rawPoint_mem L z hz,zero_add]
    simpa only [add_comm] using rawPoint_period L w ⟨z,hz⟩
  by_cases hw : w∈(pair L).lattice
  · rw [rawPoint_mem L w hw,add_zero]
    exact rawPoint_period L z ⟨w,hw⟩
  by_cases hs : z+w∈(pair L).lattice
  · have hp := rawPoint_period L (-z) ⟨z+w,hs⟩
    have hn : rawPoint L w= -rawPoint L z := by
      simpa only [neg_add_cancel_left,rawPoint_neg] using hp
    rw [rawPoint_mem L (z+w) hs,hn,add_neg_cancel]
  obtain ⟨v,hv,hzv,hdv,hdzv,hxvz,hxvzw,hxzvw⟩ :=
    WeierstrassAvoidance318.exists_auxiliary (pair L) z w
  have h1 := rawPoint_add_chord L z v hz hv (sub_ne_zero.mpr hxvz.symm) hdv
  have h2 := rawPoint_add_chord L w (z+v) hw hzv (sub_ne_zero.mpr hxzvw.symm) hdzv
  have h3 := rawPoint_add_chord L (z+w) v hs hv (sub_ne_zero.mpr hxvzw.symm) hdv
  have hc : rawPoint L (z+w)+rawPoint L v=(rawPoint L z+rawPoint L w)+rawPoint L v := by
    calc
      rawPoint L (z+w)+rawPoint L v=rawPoint L ((z+w)+v) := h3.symm
      _=rawPoint L (w+(z+v)) := by congr 1; ring
      _=rawPoint L w+rawPoint L (z+v) := h2
      _=(rawPoint L z+rawPoint L w)+rawPoint L v := by rw [h1]; abel

  exact add_right_cancel hc

theorem point_add (q r : Torus L) : point L (q+r)=point L q+point L r := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective L q
  obtain ⟨w,rfl⟩ := QuotientAddGroup.mk'_surjective L r
  simpa only [rawPoint,map_add] using rawPoint_add L z w

/-- SAME full original torus and the independently defined algebraic
elliptic point group are additively isomorphic, including infinity. -/
@[expose] def addEquiv : Torus L ≃+ (curve L).toAffine.Point where
  toEquiv := equivalence L
  map_add' := point_add L

lemma doubling (q : Torus L) : addEquiv L (q+q)=addEquiv L q+addEquiv L q :=
  (addEquiv L).map_add q q
end OriginalPeriodEllipticGroup318
