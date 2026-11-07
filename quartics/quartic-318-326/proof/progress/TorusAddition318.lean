module
public import WeierstrassAvoidance318
public section
noncomputable section
namespace TorusAddition318
open PeriodEisenstein318 LatticeInvariants318 ModularWeierstrass318 LatticeModelPoint318
set_option maxHeartbeats 0

/-- The actual Weierstrass parametrization respects addition, including all tangent,
lattice, inverse and two-torsion cases. Exceptional finite cases are reduced to ordinary
chords by a proved actual auxiliary-argument existence theorem. -/
theorem point_add (tau : UpperHalfPlane) (z w : ℂ) :
    point tau (z+w)=point tau z+point tau w := by
  by_cases hz : z ∈ (periods tau).lattice
  · rw [point_of_mem tau z hz,← WeierstrassCurve.Affine.Point.zero_def,zero_add]
    simpa only [add_comm] using point_add_period tau w ⟨z,hz⟩
  by_cases hw : w ∈ (periods tau).lattice
  · rw [point_of_mem tau w hw,← WeierstrassCurve.Affine.Point.zero_def,add_zero]
    exact point_add_period tau z ⟨w,hw⟩
  by_cases hs : z+w ∈ (periods tau).lattice
  · have hperiod := point_add_period tau (-z) ⟨z+w,hs⟩
    have hn : point tau w= -point tau z := by
      simpa only [neg_add_cancel_left,TorusPointInterface318.point_neg] using hperiod
    rw [point_of_mem tau (z+w) hs,hn,add_neg_cancel]
    rfl
  obtain ⟨v,hv,hzv,hdv,hdzv,hxvz,hxvzw,hxzvw⟩ :=
    WeierstrassAvoidance318.exists_auxiliary (periods tau) z w
  have h1 := TorusChord318.point_add_chord tau z v hz hv
    (sub_ne_zero.mpr hxvz.symm) hdv
  have h2 := TorusChord318.point_add_chord tau w (z+v) hw hzv
    (sub_ne_zero.mpr hxzvw.symm) hdzv
  have h3 := TorusChord318.point_add_chord tau (z+w) v hs hv
    (sub_ne_zero.mpr hxvzw.symm) hdv
  have hc : point tau (z+w)+point tau v=(point tau z+point tau w)+point tau v := by
    calc
      _ = point tau ((z+w)+v) := h3.symm
      _ = point tau (w+(z+v)) := by congr 1; ring
      _ = point tau w+point tau (z+v) := h2
      _ = (point tau z+point tau w)+point tau v := by rw [h1]; abel
  exact add_right_cancel hc

@[expose] def pointHom (tau : UpperHalfPlane) : ℂ →+ (curve tau).toAffine.Point where
  toFun := point tau
  map_zero' := point_of_mem tau 0 (periods tau).lattice.zero_mem
  map_add' := point_add tau

theorem torusPoint_add (tau : UpperHalfPlane)
    (q r : ℂ ⧸ (periods tau).lattice.toAddSubgroup) :
    torusPoint tau (q+r)=torusPoint tau q+torusPoint tau r := by
  induction q using Quotient.inductionOn with
  | h z =>
    induction r using Quotient.inductionOn with
    | h w =>
      change point tau (z+w)=point tau z+point tau w
      exact point_add tau z w

/-- The actual period quotient and actual normalized elliptic points are additively isomorphic.
Analytic/manifold uniformization and specified modular-fiber interpretation are separate. -/
@[expose] def torusAddEquiv (tau : UpperHalfPlane) :
    (ℂ ⧸ (periods tau).lattice.toAddSubgroup) ≃+ (curve tau).toAffine.Point where
  toEquiv := TorusBijection318.torusEquiv tau
  map_add' := torusPoint_add tau

lemma torusAddEquiv_apply (tau : UpperHalfPlane)
    (q : ℂ ⧸ (periods tau).lattice.toAddSubgroup) : torusAddEquiv tau q=torusPoint tau q := rfl

end TorusAddition318
