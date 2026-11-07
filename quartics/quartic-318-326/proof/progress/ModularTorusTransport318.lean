module
public import ModularWeierstrassScale318
public import ModularPointTransport318
public section
noncomputable section
open scoped MatrixGroups
open PeriodEisenstein318 LatticeInvariants318 LatticeModelPoint318
open ModularWeierstrass318 ModularPointTransport318 ModularLattice318 ModularWeierstrassScale318
namespace ModularTorusTransport318
set_option maxHeartbeats 0

/-- The actual model transport agrees with the genuine Weierstrass parametrization,
including the lattice/infinity branch. -/
theorem point_transport (g : SL(2,ℤ)) (tau : UpperHalfPlane) (z : ℂ) :
    slPointEquiv g tau (point tau z)=point (g•tau) (z/d g tau) := by
  by_cases hz : z ∈ (periods tau).lattice
  · rw [point_of_mem tau z hz,
      point_of_mem (g•tau) (z/d g tau) ((div_mem_lattice_iff g tau z).mpr hz)]
    rfl
  · have hn : z/d g tau ∉ (periods (g•tau)).lattice :=
      fun hh => hz ((div_mem_lattice_iff g tau z).mp hh)
    rw [point_of_notMem tau z hz,point_of_notMem (g•tau) _ hn]
    simp only [slPointEquiv,pointEquiv,Equiv.coe_fn_mk,pointMap,affinePoint,
      WeierstrassCurve.Affine.Point.mk]
    congr 1
    · simpa only [d_eq_denom] using (xCoord_scale g tau z).symm
    · simpa only [d_eq_denom] using (yCoord_scale g tau z).symm

/-- Addition preservation is derived for the actual coordinate transport, not postulated. -/
theorem point_transport_add (g : SL(2,ℤ)) (tau : UpperHalfPlane)
    (P Q : (curve tau).toAffine.Point) :
    slPointEquiv g tau (P+Q)=slPointEquiv g tau P+slPointEquiv g tau Q := by
  obtain ⟨z,rfl⟩ := TorusBijection318.point_surjective tau P
  obtain ⟨w,rfl⟩ := TorusBijection318.point_surjective tau Q
  rw [← TorusAddition318.point_add,point_transport,point_transport,point_transport,
    add_div,TorusAddition318.point_add]

@[expose] def pointAddEquiv (g : SL(2,ℤ)) (tau : UpperHalfPlane) :
    (curve tau).toAffine.Point ≃+ (curve (g•tau)).toAffine.Point where
  toEquiv := slPointEquiv g tau
  map_add' := point_transport_add g tau

/-- The actual torus change of coordinates is induced by division by c*tau+d. -/
@[expose] def torusMap (g : SL(2,ℤ)) (tau : UpperHalfPlane) :
    (ℂ ⧸ (periods tau).lattice.toAddSubgroup) →
      (ℂ ⧸ (periods (g•tau)).lattice.toAddSubgroup) :=
  Quotient.lift (fun z => QuotientAddGroup.mk (z/d g tau)) (by
    intro z w h
    apply Quotient.sound
    apply QuotientAddGroup.leftRel_apply.mpr
    have hz : -z+w ∈ (periods tau).lattice := QuotientAddGroup.leftRel_apply.mp h
    have hh := (div_mem_lattice_iff g tau (-z+w)).mpr hz
    simpa [add_div,neg_div] using hh)

lemma torusMap_mk (g : SL(2,ℤ)) (tau : UpperHalfPlane) (z : ℂ) :
    torusMap g tau (QuotientAddGroup.mk z)=QuotientAddGroup.mk (z/d g tau) := rfl

/-- The genuine quotient-point diagram commutes at every point of the actual torus. -/
theorem torus_transport (g : SL(2,ℤ)) (tau : UpperHalfPlane)
    (q : ℂ ⧸ (periods tau).lattice.toAddSubgroup) :
    pointAddEquiv g tau (torusPoint tau q)=torusPoint (g•tau) (torusMap g tau q) := by
  induction q using Quotient.inductionOn with
  | h z => exact point_transport g tau z

/-- The actual quotient map is an additive equivalence. -/
@[expose] def torusAddEquiv (g : SL(2,ℤ)) (tau : UpperHalfPlane) :
    (ℂ ⧸ (periods tau).lattice.toAddSubgroup) ≃+
      (ℂ ⧸ (periods (g•tau)).lattice.toAddSubgroup) :=
  (TorusAddition318.torusAddEquiv tau).trans
    ((pointAddEquiv g tau).trans (TorusAddition318.torusAddEquiv (g•tau)).symm)

theorem torusAddEquiv_apply (g : SL(2,ℤ)) (tau : UpperHalfPlane)
    (q : ℂ ⧸ (periods tau).lattice.toAddSubgroup) :
    torusAddEquiv g tau q=torusMap g tau q := by
  apply (TorusAddition318.torusAddEquiv (g•tau)).injective
  change TorusAddition318.torusAddEquiv (g•tau)
    ((TorusAddition318.torusAddEquiv (g•tau)).symm
      (pointAddEquiv g tau (TorusAddition318.torusAddEquiv tau q)))=_
  rw [AddEquiv.apply_symm_apply]
  exact torus_transport g tau q

end ModularTorusTransport318
