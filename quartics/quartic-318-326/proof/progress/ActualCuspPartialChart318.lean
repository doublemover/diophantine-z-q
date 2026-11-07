module
public import LocalQInverse318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318 QuotientJ318 HighQParameter318 ActualCuspHomeomorph318
open HolomorphicCuspChart318
namespace ActualCuspPartialChart318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem punctured_open : IsOpen (punctured height) :=
  isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)

@[expose] def inverseFunction (N:ℕ) (q:ℂ) : Base (image N) :=
  by
  classical
  exact if hq:q∈punctured height then (cuspHomeomorph N).symm ⟨q,hq⟩
  else quotientMap N ⟨Complex.I,by simp⟩

theorem inverseFunction_coe (N:ℕ) (q:punctured height) :
    inverseFunction N q=((cuspHomeomorph N).symm q).val := by
  simp only [inverseFunction,dite_eq_left q.property]

theorem inverseFunction_projection (N:ℕ) (tau:high height) :
    inverseFunction N (Periodic.qParam 1 tau)=quotientMap N tau := by
  change inverseFunction N (qMap height tau)=_
  rw [inverseFunction_coe,←cuspHomeomorph_projection N tau,Homeomorph.symm_apply_apply]
  rfl

/-- The homeomorphism of actual open subspaces packaged as an actual partial
chart on the quotient, with its exact source and target. -/
@[expose] def chart (N:ℕ) : OpenPartialHomeomorph (Base (image N)) ℂ where
  toFun := coordinateFunction N
  invFun := inverseFunction N
  source := neighborhood N height
  target := punctured height
  map_source' b hb := (coordinate N ⟨b,hb⟩).property
  map_target' q hq := by
    rw [show inverseFunction N q=((cuspHomeomorph N).symm ⟨q,hq⟩).val from inverseFunction_coe N ⟨q,hq⟩]
    exact ((cuspHomeomorph N).symm ⟨q,hq⟩).property
  left_inv' b hb := by
    have h:=congrArg Subtype.val ((cuspHomeomorph N).symm_apply_apply ⟨b,hb⟩)
    exact (inverseFunction_coe N (cuspHomeomorph N ⟨b,hb⟩)).trans h
  right_inv' q hq := by
    have h:=congrArg Subtype.val ((cuspHomeomorph N).apply_symm_apply ⟨q,hq⟩)
    rw [show inverseFunction N q=((cuspHomeomorph N).symm ⟨q,hq⟩).val from inverseFunction_coe N ⟨q,hq⟩]
    exact h
  continuousOn_toFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact continuous_subtype_val.comp (coordinate_continuous N)
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp (cuspHomeomorph N).symm.continuous using 1
    funext q
    exact inverseFunction_coe N q
  open_source := neighborhood_open N height
  open_target := punctured_open

@[simp] theorem chart_source (N:ℕ) : (chart N).source=neighborhood N height := rfl
@[simp] theorem chart_target (N:ℕ) : (chart N).target=punctured height := rfl
@[simp] theorem chart_apply (N:ℕ) (b:Base (image N)) : chart N b=coordinateFunction N b := rfl
@[simp] theorem chart_symm_apply (N:ℕ) (q:ℂ) : (chart N).symm q=inverseFunction N q := rfl

end ActualCuspPartialChart318
