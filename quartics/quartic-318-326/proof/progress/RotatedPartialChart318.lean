module
public import WidthLocalInverse318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318 RotatedProjection318 RotatedHomeomorph318
open scoped MatrixGroups
namespace RotatedPartialChart318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem punctured_open (w A:ℝ) : IsOpen (punctured w A) :=
  isOpen_ne.inter (isOpen_lt continuous_norm continuous_const)

@[expose] def coordinateFunction (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (b:Base (image N)) : ℂ := by
  classical
  exact if hb:b∈neighborhood N g then coordinate N hN g ⟨b,hb⟩ else 0

theorem coordinateFunction_coe (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (b:neighborhood N g) :
    coordinateFunction N hN g b=(coordinate N hN g b).val := by
  simp only [coordinateFunction,dite_eq_left b.property]

theorem coordinateFunction_projection (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (tau:high 2) :
    coordinateFunction N hN g (quotientMap N (g•tau.val))=Periodic.qParam (wReal N hN g) tau := by
  change coordinateFunction N hN g (projection N g tau).val=_
  rw [coordinateFunction_coe,coordinate_projection]
  rfl

@[expose] def inverseFunction (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (q:ℂ) : Base (image N) := by
  classical
  exact if hq:q∈punctured (wReal N hN g) 2 then (cuspHomeomorph N hN g).symm ⟨q,hq⟩
  else quotientMap N ⟨Complex.I,by simp⟩

theorem inverseFunction_coe (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (q:punctured (wReal N hN g) 2) :
    inverseFunction N hN g q=((cuspHomeomorph N hN g).symm q).val := by
  simp only [inverseFunction,dite_eq_left q.property]

theorem inverseFunction_projection (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (tau:high 2) :
    inverseFunction N hN g (Periodic.qParam (wReal N hN g) tau)=quotientMap N (g•tau.val) := by
  change inverseFunction N hN g (qMap (wReal N hN g) 2 (wReal_pos N hN g) tau)=_
  rw [inverseFunction_coe,←cuspHomeomorph_projection N hN g tau,Homeomorph.symm_apply_apply]
  rfl

/-- Every actual rotated width-q homeomorphism, packaged as a genuine partial
chart on the original quotient. -/
@[expose] def chart (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) : OpenPartialHomeomorph (Base (image N)) ℂ where
  toFun := coordinateFunction N hN g
  invFun := inverseFunction N hN g
  source := neighborhood N g
  target := punctured (wReal N hN g) 2
  map_source' b hb := by
    rw [show coordinateFunction N hN g b=(coordinate N hN g ⟨b,hb⟩).val from coordinateFunction_coe N hN g ⟨b,hb⟩]
    exact (coordinate N hN g ⟨b,hb⟩).property
  map_target' q hq := by
    rw [show inverseFunction N hN g q=((cuspHomeomorph N hN g).symm ⟨q,hq⟩).val from inverseFunction_coe N hN g ⟨q,hq⟩]
    exact ((cuspHomeomorph N hN g).symm ⟨q,hq⟩).property
  left_inv' b hb := by
    rw [show coordinateFunction N hN g b=(coordinate N hN g ⟨b,hb⟩).val from coordinateFunction_coe N hN g ⟨b,hb⟩]
    have h:=congrArg Subtype.val ((cuspHomeomorph N hN g).symm_apply_apply ⟨b,hb⟩)
    exact (inverseFunction_coe N hN g (cuspHomeomorph N hN g ⟨b,hb⟩)).trans h
  right_inv' q hq := by
    rw [show inverseFunction N hN g q=((cuspHomeomorph N hN g).symm ⟨q,hq⟩).val from inverseFunction_coe N hN g ⟨q,hq⟩,
      coordinateFunction_coe]
    exact congrArg Subtype.val ((cuspHomeomorph N hN g).apply_symm_apply ⟨q,hq⟩)
  continuousOn_toFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp (coordinate_continuous N hN g) using 1
    funext b;exact coordinateFunction_coe N hN g b
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp (cuspHomeomorph N hN g).symm.continuous using 1
    funext q;exact inverseFunction_coe N hN g q
  open_source := neighborhood_open N g
  open_target := punctured_open _ _

@[simp] theorem chart_source (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) : (chart N hN g).source=neighborhood N g := rfl
@[simp] theorem chart_target (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) : (chart N hN g).target=punctured (wReal N hN g) 2 := rfl
@[simp] theorem chart_apply (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (b:Base (image N)) : chart N hN g b=coordinateFunction N hN g b := rfl
@[simp] theorem chart_symm_apply (N:ℕ) (hN:5≤N) (g:SL(2,ℤ)) (q:ℂ) : (chart N hN g).symm q=inverseFunction N hN g q := rfl

end RotatedPartialChart318
